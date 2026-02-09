/-
  Statement and Loop Elaboration

  This module contains ALL mutually recursive elaboration functions for
  statements and loops. Mutual recursion in Lean requires all functions
  to be in the same file within a single mutual...end block.

  Includes:
  - Statement elaboration (assignments, returns, breaks, conditionals)
  - Loop elaboration (simple folds, early returns, breaks, effects, tuples)
  - Helper functions used by loops
-/

import Lean
import PredictableVerification.IR.Meirei.AST
import PredictableVerification.IR.Meirei.Analysis
import PredictableVerification.IR.Meirei.Elaborator.Context
import PredictableVerification.IR.Meirei.Elaborator.Expressions
import PredictableVerification.IR.Meirei.Elaborator.Tuples
import PredictableVerification.IR.Meirei.Elaborator.LoopHelpers

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST
open Meirei.Analysis

-- =============================================================================
-- Statement Result Type
-- =============================================================================


/-- Result of elaborating a statement -/
structure StmtResult where
  term : Term  -- The elaborated term
  isReturn : Bool := false  -- Does this statement return?
  binding : Option (Ident × Term) := none  -- Optional (var, value) binding for single variable
  isEffectfulBinding : Bool := false  -- Is this binding effectful (use ← instead of :=)?
  patternBinding : Option (Array Ident × Term) := none  -- Optional (identifiers, value) for tuple destructuring
  controlFlow : ControlFlowType := ControlFlowType.none  -- Control flow type in this statement
  deriving Inhabited

/-- Wrap a term in Option.some -/
def wrapSome (t : Term) : MacroM Term := do
  `(some $t)

/-- Wrap a term in Option.none -/
def wrapNone : MacroM Term := do
  `(none)

-- =============================================================================
-- Mutual Recursion Block
-- =============================================================================

-- Mutual recursion between all statement/loop elaboration functions
mutual

/-- Elaborate a branch of statements in effectful context -/
partial def elabEffectfulBranch (stmts : List MeireiStmt) (accVarName : Name) : ElabM Term := do
  if stmts.isEmpty then
    let accIdent ← getVar accVarName
    `(pure $accIdent)
  else
    let mut bindings : Array (Ident × Term) := #[]
    let mut finalAccExpr : Option MeireiExpr := none

    for stmt in stmts do
      match stmt with
      | MeireiStmt.effectBind bindVar funcName args => do
        let args' ← args.mapM elabExpr
        let mut callExpr ← `($(mkIdent funcName))
        if args'.isEmpty then
          callExpr ← `($callExpr ())
        else
          for arg in args' do
            callExpr ← `($callExpr $arg)
        bindings := bindings.push (mkIdent bindVar, callExpr)

      | MeireiStmt.effectCall funcName args => do
        let args' ← args.mapM elabExpr
        let mut callExpr ← `($(mkIdent funcName))
        if args'.isEmpty then
          callExpr ← `($callExpr ())
        else
          for arg in args' do
            callExpr ← `($callExpr $arg)
        let discardIdent := mkIdent `_effect
        bindings := bindings.push (discardIdent, callExpr)

      | MeireiStmt.assign name rhs =>
        if name == accVarName then
          finalAccExpr := some rhs

      | _ => pure ()

    let finalValue ← match finalAccExpr with
      | some rhs => elabExpr rhs
      | none => getVar accVarName

    let mut result ← `(pure $finalValue)

    for i in [:bindings.size] do
      let idx := bindings.size - 1 - i
      let (varIdent, callExpr) := bindings[idx]!
      result ← `($callExpr >>= fun $varIdent => $result)

    return result

/-- Elaborate the body of an effectful fold -/
partial def elabEffectfulFoldBody (body : List MeireiStmt) (accVarName : Name) : ElabM Term := do
  if body.length == 1 then
    match body[0]! with
    | MeireiStmt.ifThenElse cond thenStmts elseStmts => do
      let condTerm ← elabExpr cond
      let thenBody ← elabEffectfulBranch thenStmts accVarName
      let elseBody ← elabEffectfulBranch elseStmts accVarName
      `(if $condTerm then $thenBody else $elseBody)
    | _ =>
      elabEffectfulBranch body accVarName
  else
    elabEffectfulBranch body accVarName

/-- Helper for elaborating break loop body patterns -/
partial def elabBreakLoopBody (body : List MeireiStmt) (varName : Name) (stateIdent : Ident) : ElabM Term := do
  let currentValue ← `($stateIdent.2)

  if body.length == 2 then
    match body[0]!, body[1]! with
    | MeireiStmt.ifThen breakCond breakBody, MeireiStmt.assign _ rhs =>
      if breakBody.length == 1 then
        match breakBody[0]! with
        | MeireiStmt.break_ => do
          let condTerm ← elabExpr breakCond
          let updateExpr ← elabBreakUpdateExpr rhs varName currentValue
          `(if $condTerm then (Bool.false, $currentValue) else (Bool.true, $updateExpr))
        | _ =>
          let bodyExpr ← elabStmtList body
          `((Bool.true, $bodyExpr))
      else
        let bodyExpr ← elabStmtList body
        `((Bool.true, $bodyExpr))

    | MeireiStmt.ifThen breakCond breakBody, MeireiStmt.ifThen updateCond updateBody =>
      if breakBody.length == 1 && updateBody.length == 1 then
        match breakBody[0]!, updateBody[0]! with
        | MeireiStmt.break_, MeireiStmt.assign _ rhs => do
          let breakCondTerm ← elabExpr breakCond
          let updateCondTerm ← substituteVarInExpr updateCond varName currentValue
          let updateExpr ← elabExpr rhs
          `(if $breakCondTerm then (Bool.false, $currentValue)
            else if $updateCondTerm then (Bool.true, $updateExpr)
            else (Bool.true, $currentValue))
        | _, _ =>
          let bodyExpr ← elabStmtList body
          `((Bool.true, $bodyExpr))
      else
        let bodyExpr ← elabStmtList body
        `((Bool.true, $bodyExpr))

    | MeireiStmt.ifThenElse cond thenBody elseBody, MeireiStmt.assign _ rhs =>
      let hasBreakInThen := thenBody.length == 1 && match thenBody[0]! with | MeireiStmt.break_ => true | _ => false
      let hasBreakInElse := elseBody.length == 1 && match elseBody[0]! with
        | MeireiStmt.ifThen _ inner => inner.length == 1 && match inner[0]! with | MeireiStmt.break_ => true | _ => false
        | _ => false
      if hasBreakInThen && hasBreakInElse then
        match elseBody[0]! with
        | MeireiStmt.ifThen elseCond _ => do
          let condTerm ← elabExpr cond
          let elseCondTerm ← elabExpr elseCond
          let updateExpr ← elabBreakUpdateExpr rhs varName currentValue
          `(if $condTerm then (Bool.false, $currentValue)
            else if $elseCondTerm then (Bool.false, $currentValue)
            else (Bool.true, $updateExpr))
        | _ =>
          let bodyExpr ← elabStmtList body
          `((Bool.true, $bodyExpr))
      else
        let bodyExpr ← elabStmtList body
        `((Bool.true, $bodyExpr))

    | _, _ =>
      let bodyExpr ← elabStmtList body
      `((Bool.true, $bodyExpr))
  else
    let bodyExpr ← elabStmtList body
    `((Bool.true, $bodyExpr))

/-- Elaborate a simple fold loop (no control flow) -/
partial def elabSimpleFold
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (varName : Name)
    (varInfo : VarInfo)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  -- Get current variable value before loop
  let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
  let collTerm ← elabExpr coll

  let varIdent := mkIdent (varName.appendAfter "_0")
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")

  -- Build fold context with loop variable at version 0
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  -- Optimize simple patterns: single assignment or if-then-else with assignments
  let bodyExpr ← if body.length == 1 then
    match body[0]! with
    | MeireiStmt.assign _ rhs => elabExpr rhs
    | MeireiStmt.ifThenElse cond thenStmts elseStmts =>
      if thenStmts.length == 1 && elseStmts.length == 1 then
        match thenStmts[0]!, elseStmts[0]! with
        | MeireiStmt.assign _ thenRhs, MeireiStmt.assign _ elseRhs => do
          let condTerm ← elabExpr cond
          let thenVal ← elabExpr thenRhs
          let elseVal ← elabExpr elseRhs
          `(if $condTerm then $thenVal else $elseVal)
        | _, _ => elabStmtList body
      else
        elabStmtList body
    | _ => elabStmtList body
  else
    elabStmtList body

  -- Restore context and update variable
  set savedCtx
  let updatedVar ← updateVar varName

  let foldExpr ← `(List.foldl (fun $varIdent $loopVarIdent => $bodyExpr) $currentVar $collTerm)
  return { term := updatedVar, binding := some (updatedVar, foldExpr) }

/-- Elaborate an early return loop (find-first pattern) -/
partial def elabEarlyReturnLoop
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  let collTerm ← elabExpr coll
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")
  let accIdent := mkIdent `acc_0

  -- Build fold context with early return flag set
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true, inEarlyReturnLoop := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  -- Elaborate loop body (returns will be wrapped in Option.some)
  let bodyTerm ← elabStmtList body

  -- Restore context
  set savedCtx

  -- Build Option fold: once we have a value, stop checking
  let foldBody ← `(if Option.isSome $accIdent then $accIdent else $bodyTerm)
  let foldExpr ← `(List.foldl (fun $accIdent $loopVarIdent => $foldBody) Option.none $collTerm)

  -- Return the fold expression wrapped (will be extracted with .getD by next return statement)
  let resultIdent := mkIdent `result
  -- Mark that the next return statement should extract from this Option
  let ctx ← get
  set { ctx with pendingOptionExtraction := some (resultIdent, ← `(())) }
  return { term := resultIdent, binding := some (resultIdent, foldExpr) }

/-- Elaborate a break loop -/
partial def elabBreakLoop
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (varName : Name)
    (varInfo : VarInfo)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  -- Get current variable value before loop
  let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
  let collTerm ← elabExpr coll
  let stateIdent := mkIdent `state_0
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")

  -- Build fold context with break flag set
  -- State is (Bool, Value) where Bool indicates whether to continue
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true, inBreakLoop := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  -- Elaborate body with break handling
  let foldBody ← elabBreakLoopBody body varName stateIdent

  -- Restore context
  set savedCtx

  -- Build fold that stops when state.1 is false (break was called)
  let fullFoldBody ← `(if !($stateIdent).1 then $stateIdent else $foldBody)
  let initialState ← `((Bool.true, $currentVar))
  let foldExpr ← `(List.foldl (fun $stateIdent $loopVarIdent => $fullFoldBody) $initialState $collTerm)

  let updatedVar ← updateVar varName
  let extractedValue ← `($foldExpr.2)
  return { term := updatedVar, binding := some (updatedVar, extractedValue) }

/-- Elaborate a mixed return + accumulation loop -/
partial def elabMixedReturnLoop
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (modifiedVar : Name × VarInfo)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  let (varName, varInfo) := modifiedVar
  let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
  let collTerm ← elabExpr coll
  let stateIdent := mkIdent `state_0
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")

  -- Build fold context
  -- State is (Option ReturnValue, AccumulatorValue)
  -- - (some val, _) means early return happened with val
  -- - (none, acc) means still accumulating with acc
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  -- Special handling for mixed return + accumulation pattern
  -- Pattern: if (errorCond) { return errorValue; } ... accumulation ...
  let foldBody ← if body.length == 2 then
    match body[0]!, body[1]! with
    | MeireiStmt.ifThen cond retBody, MeireiStmt.ifThen updateCond updateBody =>
      if retBody.length == 1 && updateBody.length == 1 then
        match retBody[0]!, updateBody[0]! with
        | MeireiStmt.ret retExpr, MeireiStmt.assign _ rhs => do
          -- Pattern: if (errorCond) return error; if (updateCond) acc = acc + val;
          let condTerm ← elabExpr cond
          let retTerm ← elabExpr retExpr
          let updateCondTerm ← elabExpr updateCond
          let currentValue ← `($stateIdent.2)
          let updateTerm ← elabMixedUpdateExpr rhs varName currentValue
          `(if Option.isSome $stateIdent.1 then $stateIdent
            else if $condTerm then (some $retTerm, $stateIdent.2)
            else if $updateCondTerm then (none, $updateTerm)
            else (none, $stateIdent.2))
        | _, _ => do
          -- General case: elaborate statements
          let bodyExpr ← elabStmtList body
          `((none, $bodyExpr))
      else do
        let bodyExpr ← elabStmtList body
        `((none, $bodyExpr))
    | _, _ => do
      let bodyExpr ← elabStmtList body
      `((none, $bodyExpr))
  else do
    let bodyExpr ← elabStmtList body
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
  return { term := accumPart, patternBinding := some (#[optionPart, accumPart], stateBinding) }

/-- Elaborate an effectful loop -/
partial def elabEffectfulLoop
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (varName : Name)
    (varInfo : VarInfo)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  -- Get current variable value before loop
  let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
  let collTerm ← elabExpr coll
  let varIdent := mkIdent (varName.appendAfter "_0")
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")

  -- Build fold context with effectful flag set
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true, hasEffectfulOps := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  let bodyExpr ← elabEffectfulFoldBody body varName

  set savedCtx
  let updatedVar ← updateVar varName

  let foldExpr ← `(List.foldlM (init := $currentVar) (fun $varIdent $loopVarIdent => $bodyExpr) $collTerm)
  return { term := updatedVar, binding := some (updatedVar, foldExpr), isEffectfulBinding := true }

/-- Elaborate a tuple fold (multiple modified variables) -/
partial def elabTupleFold
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (modifiedVars : Array (Name × VarInfo))
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  -- Build initial tuple of variable values before loop
  let mut initTerms : Array Term := #[]
  for (varName, varInfo) in modifiedVars do
    let varIdent := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
    initTerms := initTerms.push varIdent

  let collTerm ← elabExpr coll

  -- Build pattern for destructuring state tuple in fold
  let mut statePattern : Array Ident := #[]
  for (varName, _) in modifiedVars do
    let varIdent := mkIdent (varName.appendAfter "_0")
    statePattern := statePattern.push varIdent

  let statePatternTuple ← buildPatternTuple statePattern

  -- Build fold context with all modified variables at version 0
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true }
  for (varName, varInfo) in modifiedVars do
    foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := MeireiType.int, currentVersion := 0 } }
  set foldCtx

  -- Elaborate all statements in loop body
  let mut stmtResults : Array StmtResult := #[]
  for stmt in body do
    let result ← elabStmt stmt
    stmtResults := stmtResults.push result

  -- Build result tuple of final variable values
  let mut resultTerms : Array Term := #[]
  for (varName, _) in modifiedVars do
    let finalVar ← getVar varName
    resultTerms := resultTerms.push finalVar

  let resultTupleVars ← buildTupleFromTerms resultTerms

  -- Build let bindings for all statement results (in reverse order)
  let mut resultTuple := resultTupleVars
  for i in [:stmtResults.size] do
    let idx := stmtResults.size - 1 - i
    let stmtResult := stmtResults[idx]!
    match stmtResult.binding with
    | some (varId, val) =>
      resultTuple ← `(let $varId := $val
        $resultTuple)
    | none => pure ()

  set savedCtx
  let mut updatedVars : Array Ident := #[]
  for (varName, _) in modifiedVars do
    let updated ← updateVar varName
    updatedVars := updatedVars.push updated

  let _updatedPattern ← buildPatternTuple updatedVars
  let initTuple ← buildTupleFromTerms initTerms
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")

  let foldExpr ← `(List.foldl (fun $statePatternTuple $loopVarIdent => $resultTuple) $initTuple $collTerm)

  return { term := updatedVars[0]!, patternBinding := some (updatedVars, foldExpr) }

/-- Elaborate a single statement -/
partial def elabStmt (stmt : MeireiStmt) : ElabM StmtResult := do
  match stmt with

  -- Variable declaration: var x : T = expr;
  | MeireiStmt.varDecl name ty init => do
    let initTerm ← elabExpr init
    let varIdent ← addVar name ty
    return { term := varIdent, binding := some (varIdent, initTerm) }

  -- Assignment: x = expr;
  | MeireiStmt.assign name rhs => do
    let rhsTerm ← elabExpr rhs
    let newVar ← updateVar name
    return { term := newVar, binding := some (newVar, rhsTerm) }

  -- Return statement: return expr;
  -- In monadic context, generates `pure expr`
  | MeireiStmt.ret expr => do
    let eTerm ← elabExpr expr
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
  | MeireiStmt.break_ => do
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
  | MeireiStmt.forLoop loopVarName coll body => do
    let savedCtx ← get

    -- Detect control flow in loop body
    let controlFlowType := detectControlFlowInList body
    let hasEffects := detectEffectfulOpsInList body

    -- Add loop variable and elaborate body to discover modified variables
    let _ ← addVar loopVarName MeireiType.int
    let _ ← elabStmtList body
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

    -- Mixed pattern: early return + variable accumulation
    -- Use accumulator type (Option ReturnValue, AccumulatorValue)
    -- - (some val, _) means early return happened with val
    -- - (none, acc) means still accumulating with acc
    if !modifiedVars.isEmpty && modifiedVars.size == 1 && controlFlowType == ControlFlowType.hasReturn then
      elabMixedReturnLoop loopVarName coll body modifiedVars[0]! savedCtx

    -- Early return pattern (find-first): no variables modified, but has return
    else if modifiedVars.isEmpty && controlFlowType == ControlFlowType.hasReturn then
      elabEarlyReturnLoop loopVarName coll body savedCtx

    -- No variables modified, just iterate for effects
    else if modifiedVars.isEmpty then
      let collTerm ← elabExpr coll
      let term ← `(let _ := $collTerm
        ())
      return { term }

    -- Single variable - generate simple fold (or break pattern if needed)
    else if modifiedVars.size == 1 then
      let (varName, varInfo) := modifiedVars[0]!

      if controlFlowType == ControlFlowType.hasBreak then
        elabBreakLoop loopVarName coll body varName varInfo savedCtx
      else if hasEffects then
        elabEffectfulLoop loopVarName coll body varName varInfo savedCtx
      else
        elabSimpleFold loopVarName coll body varName varInfo savedCtx

    -- Multiple variables - generate tuple fold
    else
      elabTupleFold loopVarName coll body modifiedVars savedCtx

  -- If-then-else statement: if (cond) { thenStmts } else { elseStmts }
  | MeireiStmt.ifThenElse cond thenStmts elseStmts => do
    let ctx ← get
    let condTerm ← elabExpr cond

    let thenCf := detectControlFlowInList thenStmts
    let elseCf := detectControlFlowInList elseStmts
    let finalCf := if thenCf != ControlFlowType.none then thenCf else elseCf

    if ctx.inBreakLoop && (thenCf == ControlFlowType.hasBreak || elseCf == ControlFlowType.hasBreak) then
      let thenTerm ← elabStmtList thenStmts
      let elseTerm ← elabStmtList elseStmts
      let term ← `(if $condTerm then $thenTerm else $elseTerm)
      return { term, controlFlow := finalCf }
    else
      let thenTerm ← elabStmtList thenStmts
      let elseTerm ← elabStmtList elseStmts
      let term ← `(if $condTerm then $thenTerm else $elseTerm)
      return { term, controlFlow := finalCf }

  -- If-then statement: if (cond) { stmts }
  | MeireiStmt.ifThen cond stmts => do
    let condTerm ← elabExpr cond
    let bodyTerm ← elabStmtList stmts
    let ctx ← get
    -- Generate appropriate else branch based on context
    let elseTerm ← if ctx.inEarlyReturnLoop then
      wrapNone  -- In early-return loops, else branch returns none
    else if ctx.inBreakLoop then
      `(())  -- In break loops, else branch continues
    else
      `(())  -- Default: empty else branch
    let term ← `(if $condTerm then $bodyTerm else $elseTerm)
    let cf := detectControlFlowInList stmts
    return { term, controlFlow := cf }

  -- Block statement: { stmts }
  | MeireiStmt.block stmts => do
    let term ← elabStmtList stmts
    return { term }

  -- Effectful call without binding: f(args);
  | MeireiStmt.effectCall name args => do
    let args' ← args.mapM elabExpr
    let mut callExpr ← `($(mkIdent name))
    if args'.isEmpty then
      callExpr ← `($callExpr ())
    else
      for arg in args' do
        callExpr ← `($callExpr $arg)
    let ctx ← get
    set { ctx with hasEffectfulOps := true }
    let discardIdent := mkIdent `_effect
    return { term := discardIdent, binding := some (discardIdent, callExpr), isEffectfulBinding := true }

  -- Effectful call with binding: x <- f(args);
  | MeireiStmt.effectBind bindVar funcName args => do
    let args' ← args.mapM elabExpr
    let mut callExpr ← `($(mkIdent funcName))
    if args'.isEmpty then
      callExpr ← `($callExpr ())
    else
      for arg in args' do
        callExpr ← `($callExpr $arg)
    let ctx ← get
    set { ctx with hasEffectfulOps := true }
    let varIdent := mkIdent bindVar
    return { term := varIdent, binding := some (varIdent, callExpr), isEffectfulBinding := true }

/-- Elaborate a sequence of statements -/
partial def elabStmtList (stmts : List MeireiStmt) : ElabM Term := do
  if stmts.isEmpty then
    `(())
  else if stmts.length == 1 then
    let result ← elabStmt stmts[0]!
    return result.term
  else
    -- Elaborate all statements first
    let stmtsArray := stmts.toArray
    let mut results : Array StmtResult := #[]
    for stmt in stmtsArray do
      let r ← elabStmt stmt
      results := results.push r

    -- Build result by chaining statements from last to first
    let lastIdx := results.size - 1
    let mut result := results[lastIdx]!.term

    -- Process statements in reverse order, building nested let bindings
    for i in [:lastIdx] do
      let idx := lastIdx - 1 - i
      let stmtResult := results[idx]!
      -- If this statement returns, it becomes the result
      if stmtResult.isReturn then
        result := stmtResult.term
      else
        -- Otherwise, bind its result and continue
        match stmtResult.binding with
        | some (varId, val) =>
          if stmtResult.isEffectfulBinding then
            -- Effectful binding: use monadic bind (>>=)
            result ← `($val >>= fun $varId => $result)
          else
            -- Pure binding: use let
            result ← `(let $varId := $val
              $result)
        | none =>
          -- Pattern binding (tuple destructuring)
          match stmtResult.patternBinding with
          | some (identArray, val) =>
            -- Destructure tuple into individual let bindings
            for _h : i in [:identArray.size] do
              let idx := identArray.size - 1 - i
              let ident := identArray[idx]!
              if idx == 0 then
                result ← `(let $ident := $val.1
                  $result)
              else if idx == 1 then
                result ← `(let $ident := $val.2
                  $result)
              else
                Macro.throwError "Tuples with more than 2 elements not yet supported"
          | none => pure ()

    return result

end

end Meirei.Elaborator
