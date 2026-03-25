/-
  Meirei AST Printing Utilities

  This module provides commands to display the Meirei AST before full elaboration.
  Useful for debugging and understanding the intermediate representation.
-/

import Lean
import Meirei.IR.Meirei.Syntax
import Meirei.IR.Meirei.Parser
import Meirei.IR.Meirei.AST
import Meirei.IR.Meirei.Elaborator.EnvExtension

open Lean

namespace Meirei

syntax "#print_meirei_ast " imp_fundef : command
syntax "#print_meirei_ast " imp_struct_def : command
syntax "#print_meirei_ast " imp_enum_def : command

elab_rules : command
  | `(command| #print_meirei_ast $fundef:imp_fundef) => do
    let ast ← Elab.liftMacroM <| Parser.parseFunDef fundef
    logInfo m!"Meirei Function Definition AST for '{ast.name}':\n{repr ast}"

elab_rules : command
  | `(command| #print_meirei_ast $sd:imp_struct_def) => do
    let ast ← Elab.liftMacroM <| Parser.parseStructDef sd
    logInfo m!"Meirei Struct Definition AST for '{ast.name}':\n{repr ast}"

elab_rules : command
  | `(command| #print_meirei_ast $ed:imp_enum_def) => do
    let ast ← Elab.liftMacroM <| Parser.parseEnumDef ed
    logInfo m!"Meirei Enum Definition AST for '{ast.name}':\n{repr ast}"

/-- Display the full elaborated Lean code for a Meirei function,
    including loop bodies that `#print` hides behind opaque constants. -/
syntax "#meirei_print " ident : command

elab_rules : command
  | `(command| #meirei_print $name:ident) => do
    let env ← getEnv
    let codeMap := meireiCodeExt.getState env
    match codeMap[name.getId]? with
    | some code =>
      logInfo m!"-- Meirei elaborated Lean code for '{name.getId}':\n{code}"
    | none =>
      throwError "No Meirei elaboration found for '{name.getId}'. \
        Make sure the function was defined using [Meirei| ... ]."

end Meirei
