/-
  Meirei AST Printing Utilities

  This module provides commands to display the Meirei AST before full elaboration.
  Useful for debugging and understanding the intermediate representation.
-/

import Lean
import PredictableVerification.IR.Meirei.Syntax
import PredictableVerification.IR.Meirei.Parser
import PredictableVerification.IR.Meirei.AST

open Lean

namespace Meirei

syntax "#print_meirei_ast " imp_fundef : command

elab_rules : command
  | `(command| #print_meirei_ast $fundef:imp_fundef) => do
    let ast ← Elab.liftMacroM <| Parser.parseFunDef fundef
    logInfo m!"Meirei Function Definition AST for '{ast.name}':\n{repr ast}"

end Meirei
