/-
  Type Declaration Elaboration

  This module handles elaboration of Meirei struct and enum definitions
  to Lean `structure` and `inductive` commands respectively.
  Works in CommandElabM to directly elaborate generated commands.
-/

import Lean
import PredictableVerification.IR.Meirei.AST

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

private def typeToLeanStr : MeireiType → String
  | .named name => toString name
  | .app f arg => s!"{typeToLeanStr f} ({typeToLeanStr arg})"

private def parseAndElabCommand (cmdStr : String) : Command.CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command cmdStr "<meirei>" with
  | .ok stx => Command.elabCommand stx
  | .error msg => throwError "Failed to parse generated command: {msg}"

/-- Elaborate a struct definition to a Lean `structure` command -/
def elabStructDef (sd : MeireiStructDef) : Command.CommandElabM Unit := do
  let fieldsStr := sd.fields.map (fun f =>
    s!"  {f.name} : {typeToLeanStr f.type}") |> String.intercalate "\n"
  let cmdStr := s!"@[ext] structure {sd.name} where\n{fieldsStr}\n  deriving Repr, BEq, Inhabited"
  parseAndElabCommand cmdStr

/-- Elaborate an enum definition to a Lean `inductive` command -/
def elabEnumDef (ed : MeireiEnumDef) : Command.CommandElabM Unit := do
  let ctorsStr := ed.ctors.map (fun ctor =>
    let paramTypes := ctor.fields.map (fun f => typeToLeanStr f.type)
    let arrowStr := if paramTypes.isEmpty then toString ed.name
      else String.intercalate " → " (paramTypes ++ [toString ed.name])
    s!"  | {ctor.name} : {arrowStr}") |> String.intercalate "\n"
  let cmdStr := s!"inductive {ed.name} where\n{ctorsStr}\n  deriving Repr, BEq, Inhabited"
  parseAndElabCommand cmdStr

end Meirei.Elaborator
