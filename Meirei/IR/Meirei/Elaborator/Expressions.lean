/-
  Expression Elaboration

  This module handles elaboration of Meirei expressions to Lean terms.
  It includes both regular expression elaboration and specialized
  substitution functions used in loop transformations.
-/

import Lean
import PredictableVerification.IR.Meirei.AST
import PredictableVerification.IR.Meirei.Elaborator.Context

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

-- =============================================================================
-- Qualified Name Detection
-- =============================================================================

/-- Walk a chain of fieldAccess nodes back to the root. Returns the base var
    name and the list of field names (in order) if the chain is rooted in a
    `MeireiExpr.var`; otherwise returns `none`. -/
private def collectFieldChain : MeireiExpr → List Name → Option (Name × List Name)
  | MeireiExpr.fieldAccess inner field, acc => collectFieldChain inner (field :: acc)
  | MeireiExpr.var base, acc => some (base, acc)
  | _, _ => none

/-- Build a qualified Lean.Name from a base name and a list of field names. -/
private def buildQualName (base : Name) (fields : List Name) : Name :=
  fields.foldl (· ++ ·) base

/-- Check whether a name looks like a qualified Lean namespace/type reference
    (starts with an uppercase letter) rather than a local variable. This mirrors
    Lean's own convention: types and namespaces are uppercase, variables are
    lowercase. We use this instead of checking `ctx.vars` because not all locals
    are tracked there (e.g. loop iterator variables are bound as fold parameters). -/
private def isQualifiedPrefix (name : Name) : Bool :=
  match name.toString.toList.head? with
  | some c => c.isUpper
  | none => false

-- =============================================================================
-- Expression Elaboration
-- =============================================================================

/-- Elaborate MeireiExpr to Lean term -/
partial def elabExpr (expr : MeireiExpr) : ElabM Term := do
  match expr with
  | MeireiExpr.intLit n =>
    if n >= 0 then
      let lit := Lean.Syntax.mkNumLit (toString n)
      return lit
    else
      let lit := Lean.Syntax.mkNumLit (toString (-n))
      `(- $lit)

  | MeireiExpr.boolLit b =>
    if b then `(true) else `(false)

  | MeireiExpr.stringLit s =>
    return Lean.Syntax.mkStrLit s

  | MeireiExpr.var name => do
    let ctx ← get
    match ctx.vars[name]? with
    | none => return mkIdent name
    | some info =>
      match info.origIdent with
      | some origIdent =>
        return origIdent
      | none =>
        return mkIdent (info.name.appendAfter s!"_{info.currentVersion}")

  | MeireiExpr.binOp op lhs rhs => do
    let lhs' ← elabExpr lhs
    let rhs' ← elabExpr rhs
    match op with
    | BinOp.add => `($lhs' + $rhs')
    | BinOp.sub => `($lhs' - $rhs')
    | BinOp.mul => `($lhs' * $rhs')
    | BinOp.div => `($lhs' / $rhs')
    | BinOp.mod => `($lhs' % $rhs')
    | BinOp.gt  => `($lhs' > $rhs')
    | BinOp.lt  => `($lhs' < $rhs')
    | BinOp.ge  => `($lhs' >= $rhs')
    | BinOp.le  => `($lhs' <= $rhs')
    | BinOp.eq  => `($lhs' == $rhs')
    | BinOp.ne  => `($lhs' != $rhs')
    | BinOp.and_    => `($lhs' && $rhs')
    | BinOp.or_     => `($lhs' || $rhs')
    | BinOp.append  => `($lhs' ++ $rhs')

  | MeireiExpr.unaryOp op operand => do
    let operand' ← elabExpr operand
    match op with
    | UnaryOp.not_ => `(!$operand')

  | MeireiExpr.call name args => do
    let args' ← args.mapM elabExpr
    let mut result ← `($(mkIdent name))
    for arg in args' do
      result ← `($result $arg)
    return result

  | MeireiExpr.fieldAccess obj fieldName => do
    -- If the chain is rooted in a non-local identifier, treat as a qualified
    -- Lean name (e.g. `Nat.zero`) rather than field projection.
    match collectFieldChain obj [fieldName] with
    | some (base, fields) =>
      if isQualifiedPrefix base then
        return mkIdent (buildQualName base fields)
      else
        let objTerm ← elabExpr obj
        let fieldIdent := mkIdent fieldName
        `($objTerm.$fieldIdent:ident)
    | none =>
      let objTerm ← elabExpr obj
      let fieldIdent := mkIdent fieldName
      `($objTerm.$fieldIdent:ident)

-- =============================================================================
-- Condition Validation
-- =============================================================================

/-- Check that all variable references in a condition expression are in scope.
    Unlike general expressions, conditions in while/if shouldn't reference
    external names — only declared variables and parameters. -/
partial def validateConditionVars (expr : MeireiExpr) : ElabM Unit := do
  match expr with
  | MeireiExpr.var name => do
    let ctx ← get
    if ctx.vars[name]?.isNone then
      throw <| Macro.Exception.error (← getRef) s!"Unknown identifier '{name}'"
  | MeireiExpr.binOp _ lhs rhs =>
    validateConditionVars lhs
    validateConditionVars rhs
  | MeireiExpr.unaryOp _ operand =>
    validateConditionVars operand
  | MeireiExpr.call _ args =>
    for arg in args do
      validateConditionVars arg
  | MeireiExpr.fieldAccess obj _ =>
    validateConditionVars obj
  | MeireiExpr.intLit _ | MeireiExpr.boolLit _ | MeireiExpr.stringLit _ => pure ()

-- =============================================================================
-- Expression Substitution (for Loop State Access)
-- =============================================================================

/-- Substitute a variable in an expression (used for loop state access) -/
partial def substituteVarInExpr (expr : MeireiExpr) (varName : Name) (replacement : Term) : ElabM Term := do
  match expr with
  | MeireiExpr.var name =>
    if name == varName then
      return replacement
    else
      elabExpr expr
  | MeireiExpr.binOp op lhs rhs => do
    let lhs' ← substituteVarInExpr lhs varName replacement
    let rhs' ← substituteVarInExpr rhs varName replacement
    match op with
    | BinOp.add => `($lhs' + $rhs')
    | BinOp.sub => `($lhs' - $rhs')
    | BinOp.mul => `($lhs' * $rhs')
    | BinOp.div => `($lhs' / $rhs')
    | BinOp.mod => `($lhs' % $rhs')
    | BinOp.gt  => `($lhs' > $rhs')
    | BinOp.lt  => `($lhs' < $rhs')
    | BinOp.ge  => `($lhs' >= $rhs')
    | BinOp.le  => `($lhs' <= $rhs')
    | BinOp.eq  => `($lhs' == $rhs')
    | BinOp.ne  => `($lhs' != $rhs')
    | BinOp.and_    => `($lhs' && $rhs')
    | BinOp.or_     => `($lhs' || $rhs')
    | BinOp.append  => `($lhs' ++ $rhs')
  | MeireiExpr.unaryOp op operand => do
    let operand' ← substituteVarInExpr operand varName replacement
    match op with
    | UnaryOp.not_ => `(!$operand')
  | MeireiExpr.intLit n =>
    if n >= 0 then
      return Lean.Syntax.mkNumLit (toString n)
    else
      let lit := Lean.Syntax.mkNumLit (toString (-n))
      `(- $lit)
  | MeireiExpr.boolLit b =>
    if b then `(true) else `(false)
  | MeireiExpr.stringLit s =>
    return Lean.Syntax.mkStrLit s
  | MeireiExpr.call name args => do
    let args' ← args.mapM (substituteVarInExpr · varName replacement)
    let mut result ← `($(mkIdent name))
    for arg in args' do
      result ← `($result $arg)
    return result
  | MeireiExpr.fieldAccess obj fieldName => do
    match collectFieldChain obj [fieldName] with
    | some (base, fields) =>
      if isQualifiedPrefix base then
        return mkIdent (buildQualName base fields)
      else
        let objTerm ← substituteVarInExpr obj varName replacement
        let fieldIdent := mkIdent fieldName
        `($objTerm.$fieldIdent:ident)
    | none =>
      let objTerm ← substituteVarInExpr obj varName replacement
      let fieldIdent := mkIdent fieldName
      `($objTerm.$fieldIdent:ident)

end Meirei.Elaborator
