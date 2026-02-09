/-
  Elaborator Core - Main Entry Point

  This module provides the main entry point for the Meirei elaborator
  and registers the macro for [Meirei| ... ] syntax.
-/

import Lean
import PredictableVerification.IR.Meirei.Syntax
import PredictableVerification.IR.Meirei.Parser
import PredictableVerification.IR.Meirei.Elaborator.Context
import PredictableVerification.IR.Meirei.Elaborator.Functions

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

-- =============================================================================
-- Main Entry Point
-- =============================================================================

/-- Main elaborator for [Meirei| ... ] syntax -/
def elabMeirei (stx : TSyntax `imp_fundef) : MacroM Term := do
  let ast ← Parser.parseFunDef stx
  let ctx : ElabContext := {}
  let (result, _) ← elabFunDef ast |>.run ctx
  return result

end Meirei.Elaborator

-- =============================================================================
-- Macro Registration
-- =============================================================================

open Meirei.Elaborator

/-- Register the elaborator for [Meirei| ... ] syntax -/
macro_rules
  | `([Meirei| $fundef:imp_fundef ]) => elabMeirei fundef
