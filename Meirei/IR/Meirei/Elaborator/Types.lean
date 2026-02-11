/-
  Type Elaboration

  This module handles elaboration of Meirei types to Lean types.
-/

import Lean
import PredictableVerification.IR.Meirei.AST

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

-- =============================================================================
-- Type Elaboration
-- =============================================================================

/-- Elaborate MeireiType to Lean type -/
def elabType (ty : MeireiType) : MacroM Term := do
  match ty with
  | MeireiType.named name => return mkIdent name
  | MeireiType.app f arg => do
    let fTy ← elabType f
    let argTy ← elabType arg
    `($fTy $argTy)

end Meirei.Elaborator
