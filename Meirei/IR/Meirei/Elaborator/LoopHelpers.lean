/-
  Loop Helper Functions

  This module contains helper functions for loop elaboration that don't
  participate in mutual recursion with statement elaboration.
  These are utilities for handling special patterns in loop bodies.
-/

import Lean
import PredictableVerification.IR.Meirei.AST
import PredictableVerification.IR.Meirei.Elaborator.Context
import PredictableVerification.IR.Meirei.Elaborator.Expressions

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

-- =============================================================================
-- Loop Update Expression Helpers
-- =============================================================================

/-- Helper for elaborating break loop update expressions -/
partial def elabBreakUpdateExpr (rhs : MeireiExpr) (varName : Name) (currentValue : Term) : ElabM Term := do
  match rhs with
  | MeireiExpr.binOp BinOp.add (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue + $eTerm)
    else
      elabExpr rhs
  | MeireiExpr.binOp BinOp.mul (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue * $eTerm)
    else
      elabExpr rhs
  | MeireiExpr.binOp BinOp.sub (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue - $eTerm)
    else
      elabExpr rhs
  | _ => elabExpr rhs

/-- Helper for mixed loop update expressions -/
partial def elabMixedUpdateExpr (rhs : MeireiExpr) (varName : Name) (currentValue : Term) : ElabM Term := do
  match rhs with
  | MeireiExpr.binOp BinOp.add (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue + $eTerm)
    else
      elabExpr rhs
  | MeireiExpr.binOp BinOp.mul (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue * $eTerm)
    else
      elabExpr rhs
  | MeireiExpr.binOp BinOp.sub (MeireiExpr.var v) e =>
    if v == varName then
      let eTerm ← elabExpr e
      `($currentValue - $eTerm)
    else
      elabExpr rhs
  | _ => elabExpr rhs

end Meirei.Elaborator
