/-
  Elaborator Core - Main Entry Point

  This module provides the main entry point for the Meirei elaborator
  and registers the term elaborator for [Meirei| ... ] syntax.
-/

import Lean
import Meirei.IR.Meirei.Syntax
import Meirei.IR.Meirei.Parser
import Meirei.IR.Meirei.Elaborator.Context
import Meirei.IR.Meirei.Elaborator.Functions
import Meirei.IR.Meirei.Elaborator.TypeDecls
import Meirei.IR.Meirei.Elaborator.EnvExtension

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
-- Elaborator Registration
-- =============================================================================

open Meirei.Elaborator Meirei.Parser Meirei

/-- Term elaborator for [Meirei| ... ]. Uses elab instead of macro_rules so we
    can pretty-print the generated syntax and store it for #meirei_print. -/
elab "[Meirei|" fundef:imp_fundef "]" : term => do
  let termStx ← liftMacroM (elabMeirei fundef)
  -- imp_fundef syntax: "def" imp_ident "(" params ")" ":" type "{" stmts "}"
  -- fundef.raw[1] is the imp_ident syntax node, extract the Name using getImpIdentName
  let funcName := Parser.getImpIdentName ⟨fundef.raw[1]!⟩
  let fmt ← Lean.PrettyPrinter.ppTerm termStx
  modifyEnv fun env => meireiCodeExt.addEntry env (funcName, toString fmt)
  Term.elabTerm termStx none

/-- Elaborate meirei_type struct to Lean structure -/
elab_rules : command
  | `(command| meirei_type $sd:imp_struct_def) => do
    let ast ← Elab.liftMacroM <| parseStructDef sd
    elabStructDef ast

/-- Elaborate meirei_type enum to Lean inductive -/
elab_rules : command
  | `(command| meirei_type $ed:imp_enum_def) => do
    let ast ← Elab.liftMacroM <| parseEnumDef ed
    elabEnumDef ast
