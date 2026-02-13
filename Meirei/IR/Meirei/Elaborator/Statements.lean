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
import PredictableVerification.IR.Meirei.Elaborator.Types

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
  -- For if-then early return guards: (condition, returnValue).
  -- elabStmtList uses this to nest the continuation in the else branch,
  -- transforming `if (c) { return v; } rest` into `if c then v else rest`.
  earlyReturn : Option (Term × Term) := none
  deriving Inhabited

/-- Wrap a term in Option.some -/
def wrapSome (t : Term) : MacroM Term := do
  `(some $t)

/-- Wrap a term in Option.none -/
def wrapNone : MacroM Term := do
  `(none)

-- =============================================================================
-- Branch Assignment Helpers (for var propagation through if/else)
-- =============================================================================

/-- Extract (varName, rhsExpr) pairs from top-level assignments in a statement list -/
private def extractAssignments (stmts : List MeireiStmt) : List (Name × MeireiExpr) :=
  stmts.filterMap fun s => match s with
  | MeireiStmt.assign name rhs => some (name, rhs)
  | _ => none

/-- Check if all statements are simple assignments -/
private def allAssignments (stmts : List MeireiStmt) : Bool :=
  stmts.all fun s => match s with
  | MeireiStmt.assign _ _ => true
  | _ => false

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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
  set foldCtx

  -- Optimize simple patterns: single assignment, if-then with assignment,
  -- or if-then-else with assignments in both branches
  let bodyExpr ← if body.length == 1 then
    match body[0]! with
    | MeireiStmt.assign _ rhs => elabExpr rhs
    | MeireiStmt.ifThen cond thenStmts =>
      -- `if (cond) { acc = expr; }` → `if cond then expr else acc`
      if thenStmts.length == 1 then
        match thenStmts[0]! with
        | MeireiStmt.assign _ thenRhs => do
          let condTerm ← elabExpr cond
          let thenVal ← elabExpr thenRhs
          `(if $condTerm then $thenVal else $varIdent)
        | _ => elabStmtList body
      else
        elabStmtList body
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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
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
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
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

/-- Build a Lean match alternative: | pattern => body -/
partial def mkMatchAlt (scrutineeTerm : Term) (ctorName : Name) (bindings : List Name) (bodyTerm : Term) (fallback : Term) : ElabM Term := do
  let ctorIdent := mkIdent ctorName
  if bindings.isEmpty then
    `(match ($scrutineeTerm) with
      | $ctorIdent => $bodyTerm
      | _ => $fallback)
  else
    let patArgs := bindings.toArray.map (fun n => (⟨mkIdent n⟩ : Term))
    let ctorPat : Term := Syntax.mkApp ⟨ctorIdent⟩ patArgs
    `(match ($scrutineeTerm) with
      | $ctorPat => $bodyTerm
      | _ => $fallback)

/-- Elaborate a match statement by building nested match terms -/
partial def elabMatchStmt (scrutinee : MeireiExpr) (arms : List (MeireiPattern × List MeireiStmt)) : ElabM StmtResult := do
  let scrutineeTerm ← elabExpr scrutinee
  let mut result : Term ← `(default)
  for (pat, body) in arms.reverse do
    match pat with
    | MeireiPattern.ctor ctorName bindings =>
      let bodyTerm ← elabStmtList body
      result ← mkMatchAlt scrutineeTerm ctorName bindings bodyTerm result
  return { term := result }

/-- Elaborate the body of an Except fold, producing an Except-wrapped result.
    Recursively processes the statement list: throw guards become
    `if cond then Except.error ... else <rest>`, varDecls become let bindings,
    and the final accumulator assignment becomes `Except.ok value`. -/
partial def elabExceptFoldBody (body : List MeireiStmt) (varName : Name) (varIdent : Ident) : ElabM Term := do
  match body with
  | [] => `(Except.ok $varIdent)
  | [stmt] =>
    match stmt with
    | MeireiStmt.assign _ rhs => do
      let rhsTerm ← elabExpr rhs
      `(Except.ok $rhsTerm)
    | MeireiStmt.ifThen cond guardBody =>
      if guardBody.length == 1 then
        match guardBody[0]! with
        | MeireiStmt.throw_ throwExpr => do
          let condTerm ← elabExpr cond
          let throwTerm ← elabExpr throwExpr
          `(if $condTerm then Except.error $throwTerm else Except.ok $varIdent)
        | _ => do
          let bodyTerm ← elabStmtList body
          `(Except.ok $bodyTerm)
      else do
        let bodyTerm ← elabStmtList body
        `(Except.ok $bodyTerm)
    | _ => do
      let bodyTerm ← elabStmtList body
      `(Except.ok $bodyTerm)
  | stmt :: rest =>
    match stmt with
    | MeireiStmt.ifThen cond guardBody =>
      if guardBody.length == 1 then
        match guardBody[0]! with
        | MeireiStmt.throw_ throwExpr => do
          let condTerm ← elabExpr cond
          let throwTerm ← elabExpr throwExpr
          let restTerm ← elabExceptFoldBody rest varName varIdent
          `(if $condTerm then Except.error $throwTerm else $restTerm)
        | _ => do
          let bodyTerm ← elabStmtList body
          `(Except.ok $bodyTerm)
      else do
        let bodyTerm ← elabStmtList body
        `(Except.ok $bodyTerm)
    | MeireiStmt.varDecl name ty init => do
      let initTerm ← elabExpr init
      let varId ← addVar name ty
      let restTerm ← elabExceptFoldBody rest varName varIdent
      `(let $varId := $initTerm; $restTerm)
    | _ => do
      let bodyTerm ← elabStmtList body
      `(Except.ok $bodyTerm)

/-- Elaborate an Except fold loop (pure Except + throw + single modified var).
    Accumulator is Except E AccType. After the fold, switches to effectful mode
    so subsequent bindings use >>= (which propagates Except.error). -/
partial def elabExceptFold
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (varName : Name)
    (varInfo : VarInfo)
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
  let collTerm ← elabExpr coll

  let varIdent := mkIdent (varName.appendAfter "_0")
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")
  let accIdent := mkIdent `acc_0

  -- Build fold context with loop variable at version 0
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
  set foldCtx

  let bodyExpr ← elabExceptFoldBody body varName varIdent

  -- Restore context and switch to effectful mode so continuation uses >>=
  -- (Except E is a monad; >>= propagates errors, pure = Except.ok)
  set { savedCtx with hasEffectfulOps := true, inExceptFunction := true }
  let updatedVar ← updateVar varName

  -- Fold: short-circuit on error, extract ok value for body
  -- Build match separately to avoid parse ambiguity in quotation
  let matchBody ← `(match ($accIdent) with
    | Except.error e => Except.error e
    | Except.ok $varIdent => $bodyExpr)
  let foldExpr ← `(List.foldl (fun $accIdent $loopVarIdent => $matchBody) (Except.ok $currentVar) $collTerm)

  return { term := updatedVar, binding := some (updatedVar, foldExpr), isEffectfulBinding := true }

/-- Elaborate the body of an Except tuple fold, producing an Except-wrapped tuple.
    Like `elabExceptFoldBody` but for multiple modified variables.
    Throw guards become `if cond then Except.error ... else <rest>`,
    varDecls become let bindings, assignments update variable versions,
    and the final result is `Except.ok (v1, v2, ...)`. -/
partial def elabExceptTupleFoldBody (body : List MeireiStmt) (modifiedVarNames : Array Name) : ElabM Term := do
  let mkOkTuple : ElabM Term := do
    let mut terms : Array Term := #[]
    for varName in modifiedVarNames do
      let varId ← getVar varName
      terms := terms.push varId
    let tuple ← buildTupleFromTerms terms
    `(Except.ok $tuple)
  match body with
  | [] => mkOkTuple
  | stmt :: rest =>
    match stmt with
    | MeireiStmt.ifThen cond guardBody =>
      if guardBody.length == 1 then
        match guardBody[0]! with
        | MeireiStmt.throw_ throwExpr => do
          let condTerm ← elabExpr cond
          let throwTerm ← elabExpr throwExpr
          let restTerm ← elabExceptTupleFoldBody rest modifiedVarNames
          `(if $condTerm then Except.error $throwTerm else $restTerm)
        | _ => do
          let bodyTerm ← elabStmtList body
          `(Except.ok $bodyTerm)
      else do
        let bodyTerm ← elabStmtList body
        `(Except.ok $bodyTerm)
    | MeireiStmt.varDecl name ty init => do
      let initTerm ← elabExpr init
      let varId ← addVar name ty
      let restTerm ← elabExceptTupleFoldBody rest modifiedVarNames
      `(let $varId := $initTerm; $restTerm)
    | MeireiStmt.assign name rhs => do
      let rhsTerm ← elabExpr rhs
      let newVarId ← updateVar name
      let restTerm ← elabExceptTupleFoldBody rest modifiedVarNames
      `(let $newVarId := $rhsTerm; $restTerm)
    | _ => do
      let bodyTerm ← elabStmtList body
      `(Except.ok $bodyTerm)

/-- Elaborate an Except tuple fold loop (pure Except + throw + multiple modified vars).
    Accumulator is Except E (T1 × T2 × ...). After the fold, switches to effectful
    mode so subsequent bindings use >>= (which propagates Except.error). -/
partial def elabExceptTupleFold
    (loopVarName : Name)
    (coll : MeireiExpr)
    (body : List MeireiStmt)
    (modifiedVars : Array (Name × VarInfo))
    (savedCtx : ElabContext)
    : ElabM StmtResult := do
  -- Build initial values for each modified var
  let mut initTerms : Array Term := #[]
  for (varName, varInfo) in modifiedVars do
    initTerms := initTerms.push (mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}"))

  let collTerm ← elabExpr coll

  -- Build pattern for destructuring the Except.ok tuple in the fold body
  let mut statePattern : Array Ident := #[]
  for (varName, _) in modifiedVars do
    statePattern := statePattern.push (mkIdent (varName.appendAfter "_0"))
  let statePatternTuple ← buildPatternTuple statePattern

  -- Build fold context with all modified variables at version 0
  let mut foldCtx := savedCtx
  foldCtx := { foldCtx with inLoop := true }
  for (varName, varInfo) in modifiedVars do
    foldCtx := { foldCtx with vars := foldCtx.vars.insert varName { varInfo with currentVersion := 0 } }
  foldCtx := { foldCtx with vars := foldCtx.vars.insert loopVarName { name := loopVarName, type := (MeireiType.named `Int), currentVersion := 0 } }
  set foldCtx

  let modifiedVarNames := modifiedVars.map (·.1)
  let bodyExpr ← elabExceptTupleFoldBody body modifiedVarNames

  -- Restore context and switch to effectful mode so continuation uses >>=
  -- (Except E is a monad; >>= propagates errors, pure = Except.ok)
  set { savedCtx with hasEffectfulOps := true, inExceptFunction := true }

  let accIdent := mkIdent `acc_0
  let loopVarIdent := mkIdent (loopVarName.appendAfter "_0")
  let initTuple ← buildTupleFromTerms initTerms

  -- Fold: short-circuit on error, destructure ok tuple for body
  let matchBody ← `(match ($accIdent) with
    | Except.error e => Except.error e
    | Except.ok $statePatternTuple => $bodyExpr)
  let foldExpr ← `(List.foldl (fun $accIdent $loopVarIdent => $matchBody) (Except.ok $initTuple) $collTerm)

  -- Update all variable versions for post-loop continuation
  let mut updatedVars : Array Ident := #[]
  for (varName, _) in modifiedVars do
    let updated ← updateVar varName
    updatedVars := updatedVars.push updated

  -- Effectful pattern binding: >>= extracts the Except.ok value, then destructure tuple
  return { term := updatedVars[0]!, patternBinding := some (updatedVars, foldExpr), isEffectfulBinding := true }

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
    else if ctx.inExceptFunction && !ctx.hasEffectfulOps then
      -- Pure Except return: wrap in Except.ok
      let okTerm ← `(Except.ok $eTerm)
      return { term := okTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }
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

  -- Throw statement: throw expr;
  -- In pure Except context, generates `Except.error expr`
  -- In effectful context, generates monadic `throw expr`
  | MeireiStmt.throw_ expr => do
    let eTerm ← elabExpr expr
    let ctx ← get
    if !ctx.inExceptFunction && !ctx.hasEffectfulOps then
      Macro.throwError "throw used outside Except-returning or effectful function"
    if ctx.hasEffectfulOps then
      let throwTerm ← `(throw $eTerm)
      return { term := throwTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }
    else
      let errorTerm ← `(Except.error $eTerm)
      return { term := errorTerm, isReturn := true, controlFlow := ControlFlowType.hasReturn }

  -- For loop: for x in collection { stmts }
  | MeireiStmt.forLoop loopVarName coll body => do
    let savedCtx ← get

    -- Detect control flow in loop body
    let controlFlowType := detectControlFlowInList body
    let hasEffects := detectEffectfulOpsInList body

    -- Add loop variable and elaborate body to discover modified variables
    let _ ← addVar loopVarName (MeireiType.named `Int)
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

    -- Except fold: pure Except function with throw in loop body
    -- Uses Except E AccType as accumulator; short-circuits on error
    let hasThrow := detectThrowOpsInList body
    if hasThrow && savedCtx.inExceptFunction && !hasEffects && modifiedVars.size == 1 then
      return ← elabExceptFold loopVarName coll body modifiedVars[0]!.1 modifiedVars[0]!.2 savedCtx

    -- Except tuple fold: pure Except function with throw + multiple modified vars
    -- Same strategy as Except fold but accumulates into a tuple
    if hasThrow && savedCtx.inExceptFunction && !hasEffects && modifiedVars.size > 1 then
      return ← elabExceptTupleFold loopVarName coll body modifiedVars savedCtx

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

  -- While loop: while (cond) { stmts } or while (cond) decreasing(expr) { stmts }
  -- Without decreasing: elaborated to inline let rec; user must use partial def.
  -- With decreasing: emits termination_by so Lean can verify termination.
  | MeireiStmt.whileLoop cond body decreasingExpr => do
    let savedCtx ← get

    -- Dry-run: elaborate body to discover modified variables
    let _ ← elabStmtList body
    let postLoopCtx ← get

    let mut modifiedVars : Array (Name × VarInfo) := #[]
    for (name, preInfo) in savedCtx.vars.toList do
      match postLoopCtx.vars[name]? with
      | some postInfo =>
        if postInfo.currentVersion > preInfo.currentVersion then
          modifiedVars := modifiedVars.push (name, preInfo)
      | none => pure ()

    set savedCtx

    if modifiedVars.isEmpty then
      Macro.throwError "while loop body does not modify any variables; loop would have no effect"

    else if modifiedVars.size == 1 then
      -- Single variable: let rec loop (v : T) : T := if cond then loop body else v
      let (varName, varInfo) := modifiedVars[0]!
      let currentVar := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
      let varIdent := mkIdent (varName.appendAfter "_0")

      let mut whileCtx := savedCtx
      whileCtx := { whileCtx with inLoop := true }
      whileCtx := { whileCtx with vars := whileCtx.vars.insert varName { varInfo with currentVersion := 0 } }
      set whileCtx

      validateConditionVars cond
      let condTerm ← elabExpr cond

      -- Re-elaborate body for single-var optimization
      let bodyExpr ← if body.length == 1 then
        match body[0]! with
        | MeireiStmt.assign _ rhs => elabExpr rhs
        | MeireiStmt.ifThen ifCond thenStmts =>
          if thenStmts.length == 1 then
            match thenStmts[0]! with
            | MeireiStmt.assign _ thenRhs => do
              let ifCondTerm ← elabExpr ifCond
              let thenVal ← elabExpr thenRhs
              `(if $ifCondTerm then $thenVal else $varIdent)
            | _ => elabStmtList body
          else
            elabStmtList body
        | MeireiStmt.ifThenElse ifCond thenStmts elseStmts =>
          if thenStmts.length == 1 && elseStmts.length == 1 then
            match thenStmts[0]!, elseStmts[0]! with
            | MeireiStmt.assign _ thenRhs, MeireiStmt.assign _ elseRhs => do
              let ifCondTerm ← elabExpr ifCond
              let thenVal ← elabExpr thenRhs
              let elseVal ← elabExpr elseRhs
              `(if $ifCondTerm then $thenVal else $elseVal)
            | _, _ => elabStmtList body
          else
            elabStmtList body
        | _ => elabStmtList body
      else
        elabStmtList body

      -- Elaborate decreasing expression in loop context (vars at version 0)
      let measureOpt ← match decreasingExpr with
        | some decrExpr => do
          let decrTerm ← elabExpr decrExpr
          let toNatId := mkIdent ``Int.toNat
          let m ← `($toNatId $decrTerm)
          pure (some m)
        | none => pure none

      set savedCtx
      let updatedVar ← updateVar varName

      let varType ← elabType varInfo.type
      let whileStx ← match measureOpt with
        | some measure => do
          -- Explicit parameter style with termination_by so Lean can
          -- verify termination and generate equational lemmas.
          let bodyWithRecCall ← `(if $condTerm then loop ($bodyExpr) else $varIdent)
          `(let rec loop ($varIdent : $varType) : $varType := $bodyWithRecCall
            termination_by $measure
            loop $currentVar)
        | none => do
          -- Lambda style without termination_by (user must use partial def)
          let loopBody ← `(fun ($varIdent : $varType) =>
            if $condTerm then loop ($bodyExpr) else $varIdent)
          let fnType ← `($varType → $varType)
          let callExpr ← `(loop $currentVar)
          `(let rec loop : $fnType := $loopBody; $callExpr)
      -- Replace hygienic 'loop' with unhygienic mkIdent so the aux def
      -- is accessible as parentDef.loop via #print
      let unhygienicLoop := (mkIdent `loop).raw
      let whileExpr : Term := ⟨whileStx.raw.rewriteBottomUp fun s =>
        if s.isIdent && s.getId.eraseMacroScopes == `loop then unhygienicLoop else s⟩
      return { term := updatedVar, binding := some (updatedVar, whileExpr) }

    else
      -- Multiple variables: let rec loop := fun (a, b) => if cond then loop body else (a, b)
      let mut initTerms : Array Term := #[]
      for (varName, varInfo) in modifiedVars do
        let varIdent := mkIdent (varName.appendAfter s!"_{varInfo.currentVersion}")
        initTerms := initTerms.push varIdent

      let mut statePattern : Array Ident := #[]
      for (varName, _) in modifiedVars do
        let varIdent := mkIdent (varName.appendAfter "_0")
        statePattern := statePattern.push varIdent

      let mut whileCtx := savedCtx
      whileCtx := { whileCtx with inLoop := true }
      for (varName, varInfo) in modifiedVars do
        whileCtx := { whileCtx with vars := whileCtx.vars.insert varName { varInfo with currentVersion := 0 } }
      set whileCtx

      validateConditionVars cond
      let condTerm ← elabExpr cond

      -- Elaborate decreasing expression at version 0 (before body bumps versions)
      let measureOpt ← match decreasingExpr with
        | some decrExpr => do
          if modifiedVars.size > 2 then
            Macro.throwError "decreasing annotation with more than 2 modified variables is not yet supported"
          let decrTerm ← elabExpr decrExpr
          let toNatId := mkIdent ``Int.toNat
          let m ← `($toNatId $decrTerm)
          pure (some m)
        | none => pure none

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

      -- Build recursive call: individual args for termination_by, tuple for partial
      let loopCall ← match measureOpt with
        | some _ => do
          let mut call : Term := ⟨mkIdent `loop⟩
          for resultTerm in resultTerms do
            call ← `($call $resultTerm)
          pure call
        | none => `(loop ($resultTupleVars))

      let mut resultBody := loopCall
      for i in [:stmtResults.size] do
        let idx := stmtResults.size - 1 - i
        let stmtResult := stmtResults[idx]!
        match stmtResult.binding with
        | some (varId, val) =>
          resultBody ← `(let $varId := $val
            $resultBody)
        | none => pure ()

      -- Build else branch: return state unchanged
      let stateReturnTerms : Array Term := statePattern.map fun id => (id : Term)
      let stateReturn ← buildTupleFromTerms stateReturnTerms

      set savedCtx
      let mut updatedVars : Array Ident := #[]
      for (varName, _) in modifiedVars do
        let updated ← updateVar varName
        updatedVars := updatedVars.push updated

      -- Build tuple type for annotation
      let mut typeTerms : Array Term := #[]
      for (_, varInfo) in modifiedVars do
        let tyTerm ← elabType varInfo.type
        typeTerms := typeTerms.push tyTerm
      let tupleType ← if typeTerms.size == 2 then
        `($(typeTerms[0]!) × $(typeTerms[1]!))
      else
        pure typeTerms[0]!

      let whileStx ← match measureOpt with
        | some measure => do
          -- Individual parameters with termination_by (2 vars)
          let v1 := statePattern[0]!
          let v2 := statePattern[1]!
          let t1 := typeTerms[0]!
          let t2 := typeTerms[1]!
          let bodyExpr ← `(if $condTerm then $resultBody else $stateReturn)
          let init1 := initTerms[0]!
          let init2 := initTerms[1]!
          `(let rec loop ($v1 : $t1) ($v2 : $t2) : $tupleType := $bodyExpr
            termination_by $measure
            loop $init1 $init2)
        | none => do
          -- Lambda style without termination_by (user must use partial def)
          let statePatternTuple ← buildPatternTuple statePattern
          let initTuple ← buildTupleFromTerms initTerms
          let fnType ← `($tupleType → $tupleType)
          let loopFn ← `(fun $statePatternTuple =>
            if $condTerm then $resultBody else $stateReturn)
          let callExpr ← `(loop $initTuple)
          `(let rec loop : $fnType := $loopFn; $callExpr)

      let unhygienicLoop := (mkIdent `loop).raw
      let whileExpr : Term := ⟨whileStx.raw.rewriteBottomUp fun s =>
        if s.isIdent && s.getId.eraseMacroScopes == `loop then unhygienicLoop else s⟩

      return { term := updatedVars[0]!, patternBinding := some (updatedVars, whileExpr) }

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
      -- Detect var modification: branches with only assignments to existing vars.
      -- Produces `let s_1 := if cond then rhs_a else rhs_b` so mutations propagate.
      let thenAssigns := extractAssignments thenStmts
      let elseAssigns := extractAssignments elseStmts
      let allAssigns := thenAssigns ++ elseAssigns
      let mut modifiedVarNames : Array Name := #[]
      for (name, _) in allAssigns do
        if !modifiedVarNames.contains name && ctx.vars.contains name then
          modifiedVarNames := modifiedVarNames.push name

      if modifiedVarNames.size == 1
         && finalCf == ControlFlowType.none
         && !ctx.inLoop
         && (allAssignments thenStmts || thenStmts.isEmpty)
         && (allAssignments elseStmts || elseStmts.isEmpty) then
        let varName := modifiedVarNames[0]!
        let thenRhs := thenAssigns.find? (fun a => a.1 == varName) |>.map (·.2)
        let elseRhs := elseAssigns.find? (fun a => a.1 == varName) |>.map (·.2)
        let currentVarTerm ← elabExpr (MeireiExpr.var varName)
        let thenVal ← match thenRhs with
          | some rhs => elabExpr rhs
          | none => pure currentVarTerm
        let elseVal ← match elseRhs with
          | some rhs => elabExpr rhs
          | none => pure currentVarTerm
        let newVar ← updateVar varName
        let ifExpr ← `(if $condTerm then $thenVal else $elseVal)
        return { term := newVar, binding := some (newVar, ifExpr), controlFlow := finalCf }
      else
        let thenTerm ← elabStmtList thenStmts
        let elseTerm ← elabStmtList elseStmts
        let term ← `(if $condTerm then $thenTerm else $elseTerm)
        return { term, controlFlow := finalCf }

  -- If-then statement: if (cond) { stmts }
  | MeireiStmt.ifThen cond stmts => do
    let ctx ← get
    let condTerm ← elabExpr cond
    let cf := detectControlFlowInList stmts

    -- Detect var modification in if-then (no else) outside loops.
    -- Produces `let s_1 := if cond then rhs else s_0`.
    let assigns := extractAssignments stmts
    let mut modifiedVarNames : Array Name := #[]
    for (name, _) in assigns do
      if !modifiedVarNames.contains name && ctx.vars.contains name then
        modifiedVarNames := modifiedVarNames.push name

    if modifiedVarNames.size == 1
       && cf == ControlFlowType.none
       && !ctx.inLoop
       && allAssignments stmts then
      let varName := modifiedVarNames[0]!
      match assigns.find? (fun a => a.1 == varName) with
      | some (_, rhs) =>
        let currentVarTerm ← elabExpr (MeireiExpr.var varName)
        let thenVal ← elabExpr rhs
        let newVar ← updateVar varName
        let ifExpr ← `(if $condTerm then $thenVal else $currentVarTerm)
        return { term := newVar, binding := some (newVar, ifExpr), controlFlow := cf }
      | none =>
        let bodyTerm ← elabStmtList stmts
        let elseTerm ← if ctx.inEarlyReturnLoop then wrapNone
          else `(())
        let term ← `(if $condTerm then $bodyTerm else $elseTerm)
        return { term, controlFlow := cf }
    else
      let bodyTerm ← elabStmtList stmts
      -- Detect complete early return guards: if the body's last statement is
      -- a return, every path through the body returns when the condition holds.
      -- Emit earlyReturn so elabStmtList can nest the continuation as the else branch.
      let lastIsEarlyExit := match stmts.getLast? with
        | some (MeireiStmt.ret _) => true
        | some (MeireiStmt.throw_ _) => true
        | _ => false
      if cf == ControlFlowType.hasReturn && lastIsEarlyExit
         && !ctx.inEarlyReturnLoop && !ctx.inBreakLoop then
        let term ← `(if $condTerm then $bodyTerm else ())
        return { term, controlFlow := cf, earlyReturn := some (condTerm, bodyTerm) }
      else
        let elseTerm ← if ctx.inEarlyReturnLoop then
          wrapNone
        else if ctx.inBreakLoop then
          `(())
        else
          `(())
        let term ← `(if $condTerm then $bodyTerm else $elseTerm)
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

  -- Match statement: match expr { case Ctor(x, y) { ... } ... }
  | MeireiStmt.match_ scrutinee arms => do
    elabMatchStmt scrutinee arms

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
      -- Early return guard: nest continuation as the else branch
      -- e.g. `if (x <= lo) { return lo; } rest` → `if x <= lo then lo else rest`
      match stmtResult.earlyReturn with
      | some (cond, retVal) =>
        result ← `(if $cond then $retVal else $result)
      | none =>
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
            -- Bind value once to a temp, then destructure (avoids duplicating let rec)
            let tmpIdent := mkIdent `_tupleResult
            for _h : i in [:identArray.size] do
              let idx := identArray.size - 1 - i
              let ident := identArray[idx]!
              if idx == 0 then
                result ← `(let $ident := $tmpIdent.1
                  $result)
              else if idx == 1 then
                result ← `(let $ident := $tmpIdent.2
                  $result)
              else
                Macro.throwError "Tuples with more than 2 elements not yet supported"
            if stmtResult.isEffectfulBinding then
              result ← `($val >>= fun $tmpIdent => $result)
            else
              result ← `(let $tmpIdent := $val
                $result)
          | none => pure ()

    return result

end

end Meirei.Elaborator
