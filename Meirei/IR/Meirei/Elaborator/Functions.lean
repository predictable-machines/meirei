/-
  Function Definition Elaboration

  This module handles elaboration of complete function definitions,
  including parameters, return types, and function bodies.
-/

import Lean
import PredictableVerification.IR.Meirei.AST
import PredictableVerification.IR.Meirei.Elaborator.Context
import PredictableVerification.IR.Meirei.Elaborator.Types
import PredictableVerification.IR.Meirei.Elaborator.Statements

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

-- =============================================================================
-- Function Definition Elaboration
-- =============================================================================

/-- Elaborate a function definition from AST -/
def elabFunDef (funDef : MeireiFunDef) : ElabM Term := do
  let _retTyTerm ← elabType funDef.returnType

  let mut paramBinders : Array (TSyntax `Lean.Parser.Term.funBinder) := #[]
  for param in funDef.params do
    let ptyTerm ← elabType param.type
    let pident := mkIdent param.name
    addParam pident param.type
    let binder ← `(Lean.Parser.Term.funBinder| ($pident : $ptyTerm))
    paramBinders := paramBinders.push binder

  let bodyTerm ← elabStmtList funDef.body

  let mut result := bodyTerm
  for binder in paramBinders.reverse do
    result ← `(fun $binder => $result)

  return result

end Meirei.Elaborator
