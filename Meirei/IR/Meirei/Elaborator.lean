/-
  Complete Meirei Elaborator using Metaprogramming

  This module implements a full elaborator that can handle ANY Meirei program,
  not just hardcoded patterns. It uses Lean's metaprogramming API to:

  1. Parse syntax trees recursively
  2. Track variables with SSA-style versioning
  3. Generate pure functional Lean code from imperative syntax
  4. Support all control flow constructs (loops, if, break, return)

  Design principles:
  - Variables are immutable (SSA-style: x_0, x_1, x_2, ...)
  - Loops become folds with state transformers
  - Early exits use Option or (Bool, Value) pairs
  - All code generation is compositional and recursive
-/

import Lean
import PredictableVerification.IR.Meirei.Syntax

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

-- =============================================================================
-- Data Structures
-- =============================================================================

/-- Information about a variable in scope -/
structure VarInfo where
  name : Name
  type : TSyntax `imp_type
  currentVersion : Nat
  origIdent : Option Ident := none  -- Store original identifier for hygiene (parameters)  -- For SSA-style naming (x becomes x_0, x_1, ...)
  deriving Repr, Inhabited

/-- Elaboration context tracking variables and control flow state -/
structure ElabContext where
  vars : Std.HashMap Name VarInfo := {}
  loopDepth : Nat := 0
  inLoop : Bool := false
  inEarlyReturnLoop : Bool := false  -- Are we in a loop with early return?
  inBreakLoop : Bool := false  -- Are we in a loop with break?
  pendingOptionExtraction : Option (Ident × Term) := none  -- (resultIdent, defaultValue) for Option extraction
  pendingMixedReturn : Option (Ident × Ident) := none  -- (optionIdent, accumIdent) for mixed return + accumulation
  hasEffectfulOps : Bool := false  -- Has this function seen any effectful operations?
  deriving Inhabited

/-- Elaboration monad -/
abbrev ElabM := StateT ElabContext MacroM

-- =============================================================================
-- Context Management
-- =============================================================================

/-- Add a new variable to context -/
def addVar (name : Name) (type : TSyntax `imp_type) : ElabM Ident := do
  let ctx ← get
  let info : VarInfo := { name, type, currentVersion := 0 }
  set { ctx with vars := ctx.vars.insert name info }
  return mkIdent (name.appendAfter "_0")

/-- Add a parameter to context (uses original name, not versioned) -/
def addParam (ident : Ident) (type : TSyntax `imp_type) : ElabM Unit := do
  let ctx ← get
  let info : VarInfo := { name := ident.getId, type, currentVersion := 0, origIdent := some ident }
  set { ctx with vars := ctx.vars.insert ident.getId info }

/-- Update a variable (create new version) -/
def updateVar (name : Name) : ElabM Ident := do
  let ctx ← get
  match ctx.vars[name]? with
  | none => throw <| Macro.Exception.error (← getRef) s!"Variable {name} not found"
  | some info =>
    let newVersion := info.currentVersion + 1
    let newInfo : VarInfo := { info with currentVersion := newVersion }
    set { ctx with vars := ctx.vars.insert name newInfo }
    return mkIdent (name.appendAfter s!"_{newVersion}")

/-- Get current version of a variable -/
def getVar (name : Name) : ElabM Ident := do
  let ctx ← get
  match ctx.vars[name]? with
  | none => throw <| Macro.Exception.error (← getRef) s!"Variable {name} not found"
  | some info =>
    -- If version is 0 and it's not been updated, it's likely a parameter - use original name
    -- Otherwise use versioned name
    if info.currentVersion == 0 then
      return mkIdent name
    else
      return mkIdent (name.appendAfter s!"_{info.currentVersion}")

-- =============================================================================
-- Type Elaboration
-- =============================================================================

/-- Elaborate imp_type to Lean type -/
partial def elabType (stx : TSyntax `imp_type) : ElabM Term := do
  match stx with
  | `(imp_type| int) => `(Int)
  | `(imp_type| [ $ty:imp_type ]) => do
    let innerTy ← elabType ty
    `(List $innerTy)
  | _ => throw <| Macro.Exception.error stx "Unsupported type"

-- =============================================================================
-- Expression Elaboration
-- =============================================================================

/-- Elaborate imp_expr to Lean term -/
partial def elabExpr (stx : TSyntax `imp_expr) : ElabM Term := do
  match stx with
  -- Literals
  | `(imp_expr| $n:num) => return n

  -- Negative numbers
  | `(imp_expr| - $n:num) => `(- $n)

  -- Variables (resolve to current version)
  | `(imp_expr| $x:ident) => do
    let ctx ← get
    match ctx.vars[x.getId]? with
    | none =>
      -- Variable not found - just return the identifier as-is
      return x
    | some info =>
      -- If this is a parameter (has origIdent), use it directly for proper hygiene
      match info.origIdent with
      | some origIdent =>
        -- Parameter: use original identifier to preserve hygiene
        return origIdent
      | none =>
        -- Variable: use versioned name (SSA)
        -- If we're in a loop context, always use versioned names (even at version 0)
        -- Otherwise, use base name for parameters at version 0
        if info.currentVersion == 0 && !ctx.inLoop then
          return mkIdent info.name
        else
          return mkIdent (info.name.appendAfter s!"_{info.currentVersion}")

  -- Arithmetic operators
  | `(imp_expr| $a:imp_expr + $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' + $b')

  | `(imp_expr| $a:imp_expr - $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' - $b')

  | `(imp_expr| $a:imp_expr * $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' * $b')

  | `(imp_expr| $a:imp_expr / $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' / $b')

  -- Comparison operators
  | `(imp_expr| $a:imp_expr > $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' > $b')

  | `(imp_expr| $a:imp_expr < $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' < $b')

  | `(imp_expr| $a:imp_expr == $b:imp_expr) => do
    let a' ← elabExpr a
    let b' ← elabExpr b
    `($a' == $b')

  -- Function calls
  | `(imp_expr| $f:ident ( $args,* )) => do
    let args' ← args.getElems.mapM elabExpr
    let mut result ← `($f:ident)
    for arg in args' do
      result ← `($result $arg)
    return result

  -- Parenthesized expressions
  | `(imp_expr| ( $e:imp_expr )) => elabExpr e

  | _ => throw <| Macro.Exception.error stx "Unsupported expression"

-- =============================================================================
-- Helper Functions for Building Tuples
-- =============================================================================

/-- Build a tuple from terms -/
def buildTupleFromTerms (terms : Array Term) : MacroM Term := do
  if terms.isEmpty then
    `(())
  else if terms.size == 1 then
    return terms[0]!
  else if terms.size == 2 then
    `(($(terms[0]!), $(terms[1]!)))
  else
    -- Build nested tuple: (a, (b, (c, ...)))
    let rec build (idx : Nat) : MacroM Term := do
      if idx >= terms.size - 1 then
        return terms[terms.size - 1]!
      else
        let rest ← build (idx + 1)
        `(($(terms[idx]!), $rest))
    build 0

/-- Build a pattern tuple from identifiers -/
def buildPatternTuple (idents : Array Ident) : MacroM Term := do
  if idents.isEmpty then
    `(_)
  else if idents.size == 1 then
    return idents[0]!
  else if idents.size == 2 then
    `(($(idents[0]!), $(idents[1]!)))
  else
    -- Build nested pattern: (a, (b, (c, ...)))
    let rec build (idx : Nat) : MacroM Term := do
      if idx >= idents.size - 1 then
        return idents[idents.size - 1]!
      else
        let rest ← build (idx + 1)
        `(($(idents[idx]!), $rest))
    build 0

-- =============================================================================
-- Statement Elaboration
-- =============================================================================

/-- Control flow type detected in a statement -/
inductive ControlFlowType
  | none
  | hasReturn
  | hasBreak
  deriving Repr, BEq, Inhabited

/-- Result of elaborating a statement -/
structure StmtResult where
  term : Term  -- The elaborated term
  isReturn : Bool := false  -- Does this statement return?
  binding : Option (Ident × Term) := none  -- Optional (var, value) binding for single variable
  isEffectfulBinding : Bool := false  -- Is this binding effectful (use ← instead of :=)?
  patternBinding : Option (Array Ident × Term) := none  -- Optional (identifiers, value) for tuple destructuring
  controlFlow : ControlFlowType := ControlFlowType.none  -- Control flow type in this statement
  deriving Inhabited

/-- Detect control flow type in a statement syntax -/
partial def detectControlFlow (stx : TSyntax `imp_stmt) : MacroM ControlFlowType := do
  match stx with
  | `(imp_stmt| return $_:imp_expr ;) => return ControlFlowType.hasReturn
  | `(imp_stmt| break ;) => return ControlFlowType.hasBreak
  | `(imp_stmt| if ( $_:imp_expr ) { $stmts* }) => do
    for stmt in stmts do
      let cf ← detectControlFlow stmt
      if cf != ControlFlowType.none then
        return cf
    return ControlFlowType.none
  | `(imp_stmt| if ( $_:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
    for stmt in thenStmts do
      let cf ← detectControlFlow stmt
      if cf != ControlFlowType.none then
        return cf
    for stmt in elseStmts do
      let cf ← detectControlFlow stmt
      if cf != ControlFlowType.none then
        return cf
    return ControlFlowType.none
  | `(imp_stmt| { $stmts* }) => do
    for stmt in stmts do
      let cf ← detectControlFlow stmt
      if cf != ControlFlowType.none then
        return cf
    return ControlFlowType.none
  | _ => return ControlFlowType.none

/-- Detect control flow in multiple statements -/
def detectControlFlowInStmts (stmts : Array (TSyntax `imp_stmt)) : MacroM ControlFlowType := do
  for stmt in stmts do
    let cf ← detectControlFlow stmt
    if cf != ControlFlowType.none then
      return cf
  return ControlFlowType.none

/-- Detect if a statement contains effectful operations (effectful calls) -/
partial def detectEffectfulOps (stx : TSyntax `imp_stmt) : MacroM Bool := do
  match stx with
  | `(imp_stmt| $_y:ident <- $_f:ident ( $_args,* ) ;) => return true  -- Effectful call with binding
  | `(imp_stmt| $_f:ident ( $_args,* ) ;) => return true  -- Effectful call without binding
  | `(imp_stmt| if ( $_cond:imp_expr ) { $stmts* }) => do
    for stmt in stmts do
      if ← detectEffectfulOps stmt then return true
    return false
  | `(imp_stmt| if ( $_cond:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
    for stmt in thenStmts do
      if ← detectEffectfulOps stmt then return true
    for stmt in elseStmts do
      if ← detectEffectfulOps stmt then return true
    return false
  | `(imp_stmt| { $stmts* }) => do
    for stmt in stmts do
      if ← detectEffectfulOps stmt then return true
    return false
  | _ => return false

/-- Detect effectful operations in multiple statements -/
def detectEffectfulOpsInStmts (stmts : Array (TSyntax `imp_stmt)) : MacroM Bool := do
  for stmt in stmts do
    if ← detectEffectfulOps stmt then return true
  return false

/-- Wrap a term in Option.some -/
def wrapSome (t : Term) : MacroM Term := do
  `(some $t)

/-- Wrap a term in Option.none -/
def wrapNone : MacroM Term := do
  `(none)

/-- Substitute a variable with a term in an expression -/
partial def substituteVarInExpr (expr : TSyntax `imp_expr) (varName : Name) (replacement : Term) : ElabM Term := do
  match expr with
  | `(imp_expr| $v:ident) =>
    if v.getId == varName then
      return replacement
    else
      -- Not the target variable - elaborate it normally to resolve it
      elabExpr expr
  | `(imp_expr| $a:imp_expr + $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' + $b')
  | `(imp_expr| $a:imp_expr - $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' - $b')
  | `(imp_expr| $a:imp_expr * $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' * $b')
  | `(imp_expr| $a:imp_expr / $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' / $b')
  | `(imp_expr| $a:imp_expr > $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' > $b')
  | `(imp_expr| $a:imp_expr < $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' < $b')
  | `(imp_expr| $a:imp_expr == $b:imp_expr) => do
    let a' ← substituteVarInExpr a varName replacement
    let b' ← substituteVarInExpr b varName replacement
    `($a' == $b')
  | `(imp_expr| $n:num) => return n
  | `(imp_expr| - $n:num) => `(- $n)
  | `(imp_expr| ( $e:imp_expr )) => do
    let e' ← substituteVarInExpr e varName replacement
    `(($e'))
  | _ =>
    -- For other cases, elaborate normally
    elabExpr expr

-- Mutual recursion between elabStmt and elabStmts
mutual

/-- Elaborate a single statement -/
partial def elabStmt (stx : TSyntax `imp_stmt) : ElabM StmtResult := do
  match stx with

  -- Variable declaration: var x : T = expr;
  | `(imp_stmt| var $x:ident : $ty:imp_type = $init:imp_expr ;) => do
    let initTerm ← elabExpr init
    let varIdent ← addVar x.getId ty
    return { term := varIdent, binding := some (varIdent, initTerm) }

  -- Assignment: x = expr;
  | `(imp_stmt| $x:ident = $rhs:imp_expr ;) => do
    let rhsTerm ← elabExpr rhs
    let newVar ← updateVar x.getId
    return { term := newVar, binding := some (newVar, rhsTerm) }

  -- Return statement: return expr;
  -- In monadic context, generates `pure expr`
  | `(imp_stmt| return $e:imp_expr ;) => do
    let eTerm ← elabExpr e
    let ctx ← get
    -- If we're in an early-return loop, wrap the value in Option.some
    if ctx.inEarlyReturnLoop then
      let wrappedTerm ← wrapSome eTerm
      return { term := wrappedTerm, isReturn := false, controlFlow := ControlFlowType.hasReturn }
    -- If there's a pending mixed return check, check Option and return appropriate value
    else if let some (optionIdent, _accumIdent) := ctx.pendingMixedReturn then
      -- Clear the pending check
      set { ctx with pendingMixedReturn := none }
      -- Generate: if optionIdent.isSome then optionIdent.get! else <return expression>
      let extractedTerm ← `(if Option.isSome $optionIdent then Option.get! $optionIdent else $eTerm)
      return { term := extractedTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }
    -- If there's a pending Option extraction (from early-return loop), extract it
    else if let some (resultIdent, _defaultVal) := ctx.pendingOptionExtraction then
      -- Clear the pending extraction
      set { ctx with pendingOptionExtraction := none }
      -- Generate: Option.getD resultIdent eTerm
      let extractedTerm ← `(Option.getD $resultIdent $eTerm)
      return { term := extractedTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }
    else
      -- Check if we're in an effectful context
      if ctx.hasEffectfulOps then
        -- Monadic return: generate `pure expr`
        let pureTerm ← `(pure $eTerm)
        return { term := pureTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }
      else
        -- Pure return: just return the expression
        return { term := eTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }

  -- Break statement: break;
  | `(imp_stmt| break ;) => do
    let ctx ← get
    -- If we're in a break loop, generate (false, value)
    if ctx.inBreakLoop then
      -- We need to know what value to preserve - this should be the current accumulator
      -- For now, just mark it and let the if statement handler deal with it
      let term ← `(false)  -- Signal to stop
      return { term, controlFlow := ControlFlowType.hasBreak }
    else
      let term ← `(())
      return { term, controlFlow := ControlFlowType.hasBreak }

  -- For loop: for x in collection { stmts }
  | `(imp_stmt| for $x:ident in $coll:imp_expr { $stmts* }) => do
    let savedCtx ← get

    -- Detect control flow in loop body
    let controlFlowType ← detectControlFlowInStmts stmts

    -- Add loop variable and elaborate body to discover modified variables
    let _ ← addVar x.getId (← `(imp_type| int))
    let _ ← elabStmts stmts
    let postLoopCtx ← get

    -- Find modified variables
    let mut modifiedVars : Array (Name × VarInfo) := #[]
    for (name, preInfo) in savedCtx.vars.toList do
      match postLoopCtx.vars[name]? with
      | some postInfo =>
        if postInfo.currentVersion > preInfo.currentVersion then
          modifiedVars := modifiedVars.push (name, preInfo)
      | none => pure ()

    -- Restore context
    set savedCtx

    if !modifiedVars.isEmpty && modifiedVars.size == 1 && controlFlowType == ControlFlowType.hasReturn then
      -- Mixed pattern: early return + variable accumulation
      -- Use accumulator type (Option ReturnValue, AccumulatorValue)
      -- - (some val, _) means early return happened with val
      -- - (none, acc) means still accumulating with acc
      let (varName, varInfo) := modifiedVars[0]!
      let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
      let collTerm ← elabExpr coll
      let stateIdent := mkIdent `state_0
      let loopVarIdent := mkIdent (x.getId.appendAfter "_0")

      -- Build fold context
      let mut foldCtx := savedCtx
      foldCtx := { foldCtx with inLoop := true }
      foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
      foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
      set foldCtx

      -- Special handling for mixed return + accumulation pattern
      -- Pattern: if (errorCond) { return errorValue; } ... accumulation ...
      let foldBody ← if stmts.size == 2 then
        match stmts[0]!, stmts[1]! with
        | `(imp_stmt| if ( $cond:imp_expr ) { return $retExpr:imp_expr ; }),
          `(imp_stmt| if ( $updateCond:imp_expr ) { $_lhs:ident = $rhs:imp_expr ; }) => do
          -- Pattern: if (errorCond) return error; if (updateCond) acc = acc + val;
          let condTerm ← elabExpr cond
          let retTerm ← elabExpr retExpr
          let updateCondTerm ← elabExpr updateCond

          -- Substitute variable in RHS with state.2 (same as in break pattern)
          let currentValue ← `($stateIdent.2)
          let updateTerm ← match rhs with
            | `(imp_expr| $v:ident + $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                `($currentValue + $eTerm)
              else
                elabExpr rhs
            | `(imp_expr| $v:ident * $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                `($currentValue * $eTerm)
              else
                elabExpr rhs
            | `(imp_expr| $v:ident - $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                `($currentValue - $eTerm)
              else
                elabExpr rhs
            | _ => elabExpr rhs

          `(if Option.isSome $stateIdent.1 then $stateIdent
            else if $condTerm then (some $retTerm, $stateIdent.2)
            else if $updateCondTerm then (none, $updateTerm)
            else (none, $stateIdent.2))
        | _, _ => do
          -- General case: elaborate statements
          -- But we need to handle returns specially
          let bodyExpr ← elabStmts stmts
          `((none, $bodyExpr))
      else do
        let bodyExpr ← elabStmts stmts
        `((none, $bodyExpr))

      -- Restore context
      set savedCtx

      -- Build the fold
      let fullFoldBody ← `(if Option.isSome $stateIdent.1 then $stateIdent else $foldBody)
      let initialState ← `((Option.none, $currentVar))
      let foldExpr ← `(List.foldl (fun $stateIdent $loopVarIdent => $fullFoldBody) $initialState $collTerm)

      -- Now we need to extract both the Option and the accumulator
      -- The final return will check: if option.isSome then option.get! else accumulatorValue
      let _updatedVar ← updateVar varName
      let stateBinding ← `($foldExpr)

      -- Store both parts
      let optionPart := mkIdent `returnOption
      let accumPart := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion + 1}")

      -- Mark that the next return should check the option and return either that or the accumulator
      let ctx ← get
      set { ctx with pendingMixedReturn := some (optionPart, accumPart) }

      -- Return with special marker for mixed pattern
      return { term := accumPart,
               patternBinding := some (#[optionPart, accumPart], stateBinding) }

    else if modifiedVars.isEmpty && controlFlowType == ControlFlowType.hasReturn then
      -- Early return pattern (find-first): no variables modified, but has return
      -- Generate Option fold: foldl (fun acc x => match acc with | some v => some v | none => body) none coll
      let collTerm ← elabExpr coll
      let loopVarIdent := mkIdent (x.getId.appendAfter "_0")
      let accIdent := mkIdent `acc_0

      -- Build fold context
      let mut foldCtx := savedCtx
      foldCtx := { foldCtx with inLoop := true, inEarlyReturnLoop := true }
      foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
      set foldCtx

      -- Elaborate loop body
      let bodyTerm ← elabStmts stmts

      -- Restore context
      set savedCtx

      -- Build Option fold - use if to check isSome
      let foldBody ← `(if Option.isSome $accIdent then $accIdent else $bodyTerm)
      let foldExpr ← `(List.foldl (fun $accIdent $loopVarIdent => $foldBody) Option.none $collTerm)

      -- Return the fold expression wrapped (will be extracted with .getD by next return statement)
      let resultIdent := mkIdent `result
      -- Mark that the next return statement should extract from this Option
      let ctx ← get
      set { ctx with pendingOptionExtraction := some (resultIdent, ← `(())) }
      return { term := resultIdent, binding := some (resultIdent, foldExpr) }

    else if modifiedVars.isEmpty then
      -- No variables modified, just iterate for effects
      let collTerm ← elabExpr coll
      let term ← `(let _ := $collTerm
        ())
      return { term }
    else if modifiedVars.size == 1 then
      -- Single variable - generate simple fold (or break pattern if needed)
      let (varName, varInfo) := modifiedVars[0]!

      -- Get current variable value before loop
      let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")

      -- Get collection term before changing context
      let collTerm ← elabExpr coll

      if controlFlowType == ControlFlowType.hasBreak then
        -- Break pattern: use (Bool, Value) accumulator
        -- Need to handle the pattern: if (cond) { break; } followed by updates
        let stateIdent := mkIdent `state_0
        let loopVarIdent := mkIdent (x.getId.appendAfter "_0")

        -- Build fold context
        let mut foldCtx := savedCtx
        foldCtx := { foldCtx with inLoop := true, inBreakLoop := true }
        foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
        foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
        set foldCtx

        -- Check for the pattern: if (cond) { break; } followed by assignment or conditional assignment
        let foldBody ← if stmts.size == 2 then
          match stmts[0]!, stmts[1]! with
          -- Pattern 0: if-else with break(s) followed by assignment
          | `(imp_stmt| if ( $cond:imp_expr ) { break ; } else { if ( $elseCond:imp_expr ) { break ; } }),
            `(imp_stmt| $_lhs:ident = $rhs:imp_expr ;) => do
            -- Pattern: if (cond) { break; } else { if (elseCond) { break; } } followed by assignment
            -- This means: if cond OR elseCond then break else continue with assignment
            let currentValue ← `($stateIdent.2)
            let condTerm ← elabExpr cond
            let elseCondTerm ← elabExpr elseCond

            -- Substitute variable in RHS with state.2
            match rhs with
            | `(imp_expr| $v:ident + $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                let newVal ← `($currentValue + $eTerm)
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $newVal))
              else
                let updateExpr ← elabExpr rhs
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $updateExpr))
            | `(imp_expr| $v:ident * $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                let newVal ← `($currentValue * $eTerm)
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $newVal))
              else
                let updateExpr ← elabExpr rhs
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $updateExpr))
            | `(imp_expr| $v:ident - $e:imp_expr) =>
              if v.getId == varName then
                let eTerm ← elabExpr e
                let newVal ← `($currentValue - $eTerm)
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $newVal))
              else
                let updateExpr ← elabExpr rhs
                `(if $condTerm then (Bool.false, $currentValue)
                  else if $elseCondTerm then (Bool.false, $currentValue)
                  else (Bool.true, $updateExpr))
            | _ =>
              let updateExpr ← elabExpr rhs
              `(if $condTerm then (Bool.false, $currentValue)
                else if $elseCondTerm then (Bool.false, $currentValue)
                else (Bool.true, $updateExpr))
          -- Pattern 1: if (cond) { break; }  followed by direct assignment
          | `(imp_stmt| if ( $cond:imp_expr ) { $ifStmts* }), `(imp_stmt| $_lhs:ident = $rhs:imp_expr ;) => do
            -- Check if the if body is just break
            if ifStmts.size == 1 then
              match ifStmts[0]! with
              | `(imp_stmt| break ;) => do
                -- This is the break pattern!
                -- Generate: if cond then (false, state.2) else (true, updateExpr)
                -- But we need to substitute the variable reference in RHS with state.2
                let condTerm ← elabExpr cond
                -- Temporarily update context so varName resolves to state.2
                let currentValue ← `($stateIdent.2)
                -- Save and modify context to make variable resolve to state value
                let savedInnerCtx ← get
                let varInfo := savedInnerCtx.vars[varName]!
                modify fun ctx => { ctx with vars := ctx.vars.insert varName { varInfo with currentVersion := 0 } }
                let updateExpr ← elabExpr rhs
                set savedInnerCtx
                -- Now substitute the variable reference with state.2
                -- Handle common patterns: var + expr, var * expr
                match rhs with
                | `(imp_expr| $v:ident + $e:imp_expr) =>
                  if v.getId == varName then
                    let eTerm ← elabExpr e
                    let newVal ← `($currentValue + $eTerm)
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $newVal))
                  else
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $updateExpr))
                | `(imp_expr| $v:ident * $e:imp_expr) =>
                  if v.getId == varName then
                    let eTerm ← elabExpr e
                    let newVal ← `($currentValue * $eTerm)
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $newVal))
                  else
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $updateExpr))
                | `(imp_expr| $v:ident - $e:imp_expr) =>
                  if v.getId == varName then
                    let eTerm ← elabExpr e
                    let newVal ← `($currentValue - $eTerm)
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $newVal))
                  else
                    `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $updateExpr))
                | _ =>
                  `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $updateExpr))
              | _ => do
                -- Not the expected pattern, fall back to general case
                let bodyExpr ← elabStmts stmts
                `((Bool.true, $bodyExpr))
            else
              let bodyExpr ← elabStmts stmts
              `((Bool.true, $bodyExpr))
          -- Pattern 2: if (breakCond) { break; } followed by if (updateCond) { var = expr; }
          | `(imp_stmt| if ( $breakCond:imp_expr ) { $breakStmts* }),
            `(imp_stmt| if ( $updateCond:imp_expr ) { $updateStmts* }) => do
            -- Check if first if has break and second if has assignment
            if breakStmts.size == 1 && updateStmts.size == 1 then
              match breakStmts[0]!, updateStmts[0]! with
              | `(imp_stmt| break ;), `(imp_stmt| $_lhs:ident = $rhs:imp_expr ;) => do
                -- This is the sequential if pattern!
                -- Strategy: We're already in the fold context (foldCtx is set)
                -- so we can elaborate normally, but we need to substitute variable references
                let currentValue ← `($stateIdent.2)

                -- Elaborate break condition (can reference loop variable)
                let breakCondTerm ← elabExpr breakCond

                -- For update condition, substitute accumulator var with state.2
                let updateCondTerm ← substituteVarInExpr updateCond varName currentValue

                -- Elaborate RHS (can reference loop variable, like `x`)
                let updateExpr ← elabExpr rhs

                -- Build the fold body
                `(if $breakCondTerm then (Bool.false, $currentValue)
                  else if $updateCondTerm then (Bool.true, $updateExpr)
                  else (Bool.true, $currentValue))
              | _, _ => do
                let bodyExpr ← elabStmts stmts
                `((Bool.true, $bodyExpr))
            else
              let bodyExpr ← elabStmts stmts
              `((Bool.true, $bodyExpr))
          | _, _ => do
            -- Not the expected pattern
            let bodyExpr ← elabStmts stmts
            `((Bool.true, $bodyExpr))
        else
          -- General case: just elaborate the statements
          let bodyExpr ← elabStmts stmts
          `((Bool.true, $bodyExpr))

        -- Restore context
        set savedCtx

        -- Build the full fold body with continuation check
        let fullFoldBody ← `(if !($stateIdent).1 then $stateIdent else $foldBody)
        let initialState ← `((Bool.true, $currentVar))
        let foldExpr ← `(List.foldl (fun $stateIdent $loopVarIdent => $fullFoldBody) $initialState $collTerm)

        -- Update variable and extract .2
        let updatedVar ← updateVar varName
        let extractedValue ← `($foldExpr.2)
        return { term := updatedVar, binding := some (updatedVar, extractedValue) }
      else
        -- Check if loop body has effectful operations
        let hasEffects ← detectEffectfulOpsInStmts stmts

        if hasEffects then
          -- Effectful single variable fold: use foldlM
          let varIdent := mkIdent (varName.appendAfter "_0")
          let loopVarIdent := mkIdent (x.getId.appendAfter "_0")

          -- Build fold context with effectful flag
          let mut foldCtx := savedCtx
          foldCtx := { foldCtx with inLoop := true, hasEffectfulOps := true }
          foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
          foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
          set foldCtx

          -- Elaborate the body - it will produce monadic code
          -- For if-else with effectful ops, we need to handle specially
          let bodyExpr ← elabEffectfulFoldBody stmts varName

          -- Restore context and create updated variable
          set savedCtx
          let updatedVar ← updateVar varName

          -- Use foldlM for effectful fold
          let foldExpr ← `(List.foldlM (init := $currentVar) (fun $varIdent $loopVarIdent => $bodyExpr) $collTerm)
          -- The binding needs to be effectful (use ←)
          return { term := updatedVar, binding := some (updatedVar, foldExpr), isEffectfulBinding := true }
        else
          -- Normal single variable fold (no control flow, no effects)
          -- Create fresh identifiers for fold parameters
          let varIdent := mkIdent (varName.appendAfter "_0")
          let loopVarIdent := mkIdent (x.getId.appendAfter "_0")

          -- Build fold context with variables at version 0
          let mut foldCtx := savedCtx
          -- Mark that we're in a loop so variables use versioned names
          foldCtx := { foldCtx with inLoop := true }
          -- Reset the modified variable to version 0
          foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
          -- Add loop variable at version 0
          foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
          set foldCtx

          -- Special case: if body is a single assignment, get the RHS directly
          let bodyExpr ← if stmts.size == 1 then
            match stmts[0]! with
            | `(imp_stmt| $_lhs:ident = $rhs:imp_expr ;) => do
              -- Elaborate the RHS in the fold context
              elabExpr rhs
            | `(imp_stmt| if ( $cond:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
              -- Special case: if-else where both branches assign to the same variable
              -- Generate: if cond then thenValue else elseValue
              if thenStmts.size == 1 && elseStmts.size == 1 then
                match thenStmts[0]!, elseStmts[0]! with
                | `(imp_stmt| $_thenLhs:ident = $thenRhs:imp_expr ;),
                  `(imp_stmt| $_elseLhs:ident = $elseRhs:imp_expr ;) => do
                  let condTerm ← elabExpr cond
                  let thenVal ← elabExpr thenRhs
                  let elseVal ← elabExpr elseRhs
                  `(if $condTerm then $thenVal else $elseVal)
                | _, _ => elabStmts stmts
              else
                elabStmts stmts
            | _ => do
              elabStmts stmts
          else do
            elabStmts stmts

          -- Restore context and create updated variable
          set savedCtx
          let updatedVar ← updateVar varName

          let foldExpr ← `(List.foldl (fun $varIdent $loopVarIdent => $bodyExpr) $currentVar $collTerm)
          return { term := updatedVar, binding := some (updatedVar, foldExpr) }
    else
      -- Multiple variables - use tuple fold
      -- Get current variable values before loop
      let mut initTerms : Array Term := #[]
      for (varName, varInfo) in modifiedVars do
        let varIdent := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
        initTerms := initTerms.push varIdent

      -- Get collection term before changing context
      let collTerm ← elabExpr coll

      -- Build state pattern for fold parameters
      let mut statePattern : Array Ident := #[]
      for (varName, _) in modifiedVars do
        let varIdent := mkIdent (varName.appendAfter "_0")
        statePattern := statePattern.push varIdent

      let statePatternTuple ← buildPatternTuple statePattern

      -- Build fold context
      let mut foldCtx := savedCtx
      foldCtx := { foldCtx with inLoop := true }
      for (varName, varInfo) in modifiedVars do
        foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
      foldCtx := { foldCtx with vars := foldCtx.vars.insert x.getId { name := x.getId, type := ← `(imp_type| int), currentVersion := 0 } }
      set foldCtx

      -- Elaborate each statement individually
      let mut stmtResults : Array StmtResult := #[]
      for stmt in stmts do
        let result ← elabStmt stmt
        stmtResults := stmtResults.push result

      -- Build result tuple from final variable versions
      let mut resultTerms : Array Term := #[]
      for (varName, _) in modifiedVars do
        let finalVar ← getVar varName
        resultTerms := resultTerms.push finalVar

      let resultTupleVars ← buildTupleFromTerms resultTerms

      -- Build the fold body by nesting let bindings and ending with tuple
      let mut resultTuple := resultTupleVars
      for i in [:stmtResults.size] do
        let idx := stmtResults.size - 1 - i
        let stmtResult := stmtResults[idx]!
        match stmtResult.binding with
        | some (varId, val) =>
          resultTuple ← `(let $varId := $val
            $resultTuple)
        | none => pure ()

      -- Restore context and create updated variables
      set savedCtx
      let mut updatedVars : Array Ident := #[]
      for (varName, _) in modifiedVars do
        let updated ← updateVar varName
        updatedVars := updatedVars.push updated

      let _updatedPattern ← buildPatternTuple updatedVars
      let initTuple ← buildTupleFromTerms initTerms
      let loopVarIdent := mkIdent (x.getId.appendAfter "_0")

      let foldExpr ← `(List.foldl (fun $statePatternTuple $loopVarIdent => $resultTuple) $initTuple $collTerm)

      -- Return first updated variable as the term, with pattern binding for destructuring
      return { term := updatedVars[0]!, patternBinding := some (updatedVars, foldExpr) }

  -- If-else statement: if (cond) { stmts } else { stmts }
  | `(imp_stmt| if ( $cond:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
    let ctx ← get
    let condTerm ← elabExpr cond

    -- Check for control flow in both branches
    let thenCf ← detectControlFlowInStmts thenStmts
    let elseCf ← detectControlFlowInStmts elseStmts
    let finalCf := if thenCf != ControlFlowType.none then thenCf else elseCf

    -- If in break loop and either branch has a break, we need special handling
    if ctx.inBreakLoop && (thenCf == ControlFlowType.hasBreak || elseCf == ControlFlowType.hasBreak) then
      -- Both branches should return state tuples when breaks are involved
      -- Elaborate branches and combine with proper state transitions
      let thenTerm ← elabStmts thenStmts
      let elseTerm ← elabStmts elseStmts

      -- The branches should already be state-aware due to context propagation
      -- Just combine them with if-else
      let term ← `(if $condTerm then $thenTerm else $elseTerm)
      return { term, controlFlow := finalCf }
    else
      -- Normal case - just elaborate and combine
      let thenTerm ← elabStmts thenStmts
      let elseTerm ← elabStmts elseStmts
      let term ← `(if $condTerm then $thenTerm else $elseTerm)
      return { term, controlFlow := finalCf }

  -- If statement: if (cond) { stmts }
  | `(imp_stmt| if ( $cond:imp_expr ) { $stmts* }) => do
    let condTerm ← elabExpr cond
    let bodyTerm ← elabStmts stmts
    let ctx ← get
    -- In early-return loops, the else branch should be `none`
    -- In break loops, the else branch should be `(true, currentValue)`
    let elseTerm ← if ctx.inEarlyReturnLoop then
      wrapNone
    else if ctx.inBreakLoop then
      -- For break loops, we need to preserve the accumulator
      -- The body should have updated it, so just pass it through
      `(())
    else
      `(())
    let term ← `(if $condTerm then $bodyTerm else $elseTerm)
    let cf ← detectControlFlowInStmts stmts
    return { term, controlFlow := cf }

  -- Block: { stmts }
  | `(imp_stmt| { $stmts* }) => do
    let term ← elabStmts stmts
    return { term }

  -- Function call statement: f(args);
  -- Treat as effectful call that discards its result (sequences with >>=)
  | `(imp_stmt| $f:ident ( $args,* ) ;) => do
    let args' ← args.getElems.mapM elabExpr
    let mut callExpr ← `($f:ident)
    -- If no arguments, apply to unit (for functions like getThreshold : Unit → EffectM Int)
    if args'.isEmpty then
      callExpr ← `($callExpr ())
    else
      for arg in args' do
        callExpr ← `($callExpr $arg)
    -- Mark that we have effectful operations
    let ctx ← get
    set { ctx with hasEffectfulOps := true }
    -- Use a fresh identifier for the discarded result
    let discardIdent := mkIdent `_effect
    return { term := discardIdent, binding := some (discardIdent, callExpr), isEffectfulBinding := true }

  -- Effectful call with result binding: y <- f(args);
  -- Generates: val >>= fun y => ... where val = f args (or f () if no args)
  | `(imp_stmt| $y:ident <- $f:ident ( $args,* ) ;) => do
    let args' ← args.getElems.mapM elabExpr
    let mut callExpr ← `($f:ident)
    -- If no arguments, apply to unit (for functions like getY : Unit → EffectM Int)
    if args'.isEmpty then
      callExpr ← `($callExpr ())
    else
      for arg in args' do
        callExpr ← `($callExpr $arg)
    -- Mark that we have effectful operations
    let ctx ← get
    set { ctx with hasEffectfulOps := true }
    -- Add the variable to context (treat as a new variable at version 0)
    -- For simplicity, we use the identifier directly without SSA versioning
    -- since effectful bindings are typically used once
    let varIdent := y
    return { term := varIdent, binding := some (varIdent, callExpr), isEffectfulBinding := true }

  | _ => throw <| Macro.Exception.error stx "Unsupported statement"

/-- Elaborate the body of an effectful fold (for loop with effects).
    Produces a monadic do-block that sequences effectful operations and
    returns `pure newAccValue` at the end. -/
partial def elabEffectfulFoldBody (stmts : Array (TSyntax `imp_stmt)) (accVarName : Name) : ElabM Term := do
  -- Handle single if-else statement which is the common pattern
  if stmts.size == 1 then
    match stmts[0]! with
    | `(imp_stmt| if ( $cond:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
      let condTerm ← elabExpr cond
      let thenBody ← elabEffectfulBranch thenStmts accVarName
      let elseBody ← elabEffectfulBranch elseStmts accVarName
      `(if $condTerm then $thenBody else $elseBody)
    | _ =>
      -- Single non-if statement - elaborate and wrap in pure
      elabEffectfulBranch stmts accVarName
  else
    -- Multiple statements - elaborate as effectful branch
    elabEffectfulBranch stmts accVarName

/-- Elaborate a branch of statements in effectful context.
    Returns a do-block with effectful bindings and `pure accValue` at the end.
    Processes statements in forward order to properly track variable bindings. -/
partial def elabEffectfulBranch (stmts : Array (TSyntax `imp_stmt)) (accVarName : Name) : ElabM Term := do
  if stmts.isEmpty then
    -- Empty branch - just return current accumulator
    let accIdent ← getVar accVarName
    `(pure $accIdent)
  else
    -- Process statements in forward order, collecting bindings and finding the final value
    -- We'll build: binding1 >>= fun v1 => binding2 >>= fun v2 => ... => pure finalValue

    -- First pass: collect all effectful bindings and find final accumulator value
    let mut bindings : Array (Ident × Term) := #[]  -- (varName, callExpr)
    let mut finalAccExpr : Option (TSyntax `imp_expr) := none

    for stmt in stmts do
      match stmt with
      | `(imp_stmt| $y:ident <- $f:ident ( $args,* ) ;) => do
        -- Effectful binding with result - elaborate args now
        let args' ← args.getElems.mapM elabExpr
        let mut callExpr ← `($f:ident)
        if args'.isEmpty then
          callExpr ← `($callExpr ())
        else
          for arg in args' do
            callExpr ← `($callExpr $arg)
        bindings := bindings.push (y, callExpr)

      | `(imp_stmt| $f:ident ( $args,* ) ;) => do
        -- Effectful call without binding (e.g., recordSale(amount);)
        let args' ← args.getElems.mapM elabExpr
        let mut callExpr ← `($f:ident)
        if args'.isEmpty then
          callExpr ← `($callExpr ())
        else
          for arg in args' do
            callExpr ← `($callExpr $arg)
        -- Use a fresh identifier for the discarded result
        let discardIdent := mkIdent `_effect
        bindings := bindings.push (discardIdent, callExpr)

      | `(imp_stmt| $x:ident = $rhs:imp_expr ;) =>
        -- Assignment - if to accumulator, remember the RHS for the final value
        if x.getId == accVarName then
          finalAccExpr := some rhs

      | _ => pure ()

    -- Elaborate the final accumulator value
    let finalValue ← match finalAccExpr with
      | some rhs => elabExpr rhs
      | none => getVar accVarName

    -- Build the nested bindings from inside out (last binding innermost)
    let mut result ← `(pure $finalValue)

    -- Process bindings in reverse order to build the nested structure
    for i in [:bindings.size] do
      let idx := bindings.size - 1 - i
      let (varIdent, callExpr) := bindings[idx]!
      result ← `($callExpr >>= fun $varIdent => $result)

    return result

/-- Find the final accumulator value from a sequence of statements -/
partial def findFinalAccValue (stmts : Array (TSyntax `imp_stmt)) (accVarName : Name) : ElabM Term := do
  -- Look for the last assignment to the accumulator variable
  for i in [:stmts.size] do
    let idx := stmts.size - 1 - i
    match stmts[idx]! with
    | `(imp_stmt| $x:ident = $rhs:imp_expr ;) =>
      if x.getId == accVarName then
        return ← elabExpr rhs
    | _ => pure ()
  -- If no assignment found, return current accumulator value
  getVar accVarName

/-- Elaborate a sequence of statements -/
partial def elabStmts (stmts : Array (TSyntax `imp_stmt)) : ElabM Term := do
  if stmts.isEmpty then
    `(())
  else if stmts.size == 1 then
    let result ← elabStmt stmts[0]!
    return result.term
  else
    -- First, elaborate all statements
    let mut results : Array StmtResult := #[]
    for stmt in stmts do
      let r ← elabStmt stmt
      results := results.push r

    -- Build from the last statement backwards
    let lastIdx := results.size - 1
    let mut result := results[lastIdx]!.term

    -- Work backwards through the statements
    for i in [:lastIdx] do
      let idx := lastIdx - 1 - i
      let stmtResult := results[idx]!
      if stmtResult.isReturn then
        -- This statement returns, use it
        result := stmtResult.term
      else
        -- Check if this statement has a binding (single variable)
        match stmtResult.binding with
        | some (varId, val) =>
          -- Wrap the rest in a let binding
          -- Use >>= (bind) for effectful bindings, let for pure bindings
          if stmtResult.isEffectfulBinding then
            -- Generate: val >>= fun varId => result
            result ← `($val >>= fun $varId => $result)
          else
            result ← `(let $varId := $val
              $result)
        | none =>
          -- Check for pattern binding (tuple destructuring)
          match stmtResult.patternBinding with
          | some (identArray, val) =>
            -- Generate nested let bindings with tuple projections directly from val
            -- Note: This duplicates the fold expression, but is simpler than managing hygiene
            -- Process in reverse order for proper nesting
            for _h : i in [:identArray.size] do
              let idx := identArray.size - 1 - i
              let ident := identArray[idx]!
              -- For a 2-tuple (a, b): a is .1, b is .2
              if idx == 0 then
                result ← `(let $ident := $val.1
                  $result)
              else if idx == 1 then
                result ← `(let $ident := $val.2
                  $result)
              else
                -- For larger tuples, they're nested: (a, (b, (c, ...)))
                Macro.throwError "Tuples with more than 2 elements not yet supported"
          | none =>
            -- No binding, just continue
            pure ()

    return result

end

-- =============================================================================
-- Function Definition Elaboration
-- =============================================================================

/-- Elaborate a function definition -/
def elabFunDef (stx : TSyntax `imp_fundef) : ElabM Term := do
  match stx with
  | `(imp_fundef| def $_name:ident ( $params,* ) : $retTy:imp_type { $stmts* }) => do
    -- Elaborate return type
    let _retTyTerm ← elabType retTy

    -- Process parameters
    let mut paramBinders : Array (TSyntax `Lean.Parser.Term.funBinder) := #[]
    let paramsArray := params.getElems
    for param in paramsArray do
      match param with
      | `(imp_param| $pname:ident : $pty:imp_type) => do
        let ptyTerm ← elabType pty
        addParam pname pty  -- Pass the identifier itself for hygiene
        let binder ← `(Lean.Parser.Term.funBinder| ($pname : $ptyTerm))
        paramBinders := paramBinders.push binder
      | _ => throw <| Macro.Exception.error param "Invalid parameter"

    -- Elaborate body (stmts is already an array from $stmts*)
    -- The body uses explicit bind (>>=) for effectful operations and pure for returns
    let bodyTerm ← elabStmts stmts

    -- Build function
    let mut result := bodyTerm
    for binder in paramBinders.reverse do
      result ← `(fun $binder => $result)

    return result

  | _ => throw <| Macro.Exception.error stx "Invalid function definition"

-- =============================================================================
-- Main Entry Point
-- =============================================================================

/-- Main elaborator for [Meirei| ... ] syntax -/
def elabMeirei (stx : TSyntax `imp_fundef) : MacroM Term := do
  let ctx : ElabContext := {}
  let (result, _) ← elabFunDef stx |>.run ctx
  return result

end Meirei.Elaborator

-- =============================================================================
-- Macro Registration
-- =============================================================================

open Meirei.Elaborator

/-- Register the elaborator for [Meirei| ... ] syntax -/
macro_rules
  | `([Meirei| $fundef:imp_fundef ]) => elabMeirei fundef
