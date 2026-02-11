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
    | BinOp.gt => `($lhs' > $rhs')
    | BinOp.lt => `($lhs' < $rhs')
    | BinOp.eq => `($lhs' == $rhs')

  | MeireiExpr.call name args => do
    let args' ← args.mapM elabExpr
    let mut result ← `($(mkIdent name))
    for arg in args' do
      result ← `($result $arg)
    return result

  | MeireiExpr.fieldAccess obj fieldName => do
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
  | MeireiExpr.call _ args =>
    for arg in args do
      validateConditionVars arg
  | MeireiExpr.fieldAccess obj _ =>
    validateConditionVars obj
  | MeireiExpr.intLit _ | MeireiExpr.stringLit _ => pure ()

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
    | BinOp.gt => `($lhs' > $rhs')
    | BinOp.lt => `($lhs' < $rhs')
    | BinOp.eq => `($lhs' == $rhs')
  | MeireiExpr.intLit n =>
    if n >= 0 then
      return Lean.Syntax.mkNumLit (toString n)
    else
      let lit := Lean.Syntax.mkNumLit (toString (-n))
      `(- $lit)
  | MeireiExpr.stringLit s =>
    return Lean.Syntax.mkStrLit s
  | MeireiExpr.call name args => do
    let args' ← args.mapM (substituteVarInExpr · varName replacement)
    let mut result ← `($(mkIdent name))
    for arg in args' do
      result ← `($result $arg)
    return result
  | MeireiExpr.fieldAccess obj fieldName => do
    let objTerm ← substituteVarInExpr obj varName replacement
    let fieldIdent := mkIdent fieldName
    `($objTerm.$fieldIdent:ident)

end Meirei.Elaborator
