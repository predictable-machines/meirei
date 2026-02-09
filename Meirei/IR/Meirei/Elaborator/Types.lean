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
  | MeireiType.int => `(Int)
  | MeireiType.list inner => do
    let innerTy ← elabType inner
    `(List $innerTy)

end Meirei.Elaborator
