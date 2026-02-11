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
  let retTyTerm ← elabType funDef.returnType

  let mut paramBinders : Array (TSyntax `Lean.Parser.Term.funBinder) := #[]
  for param in funDef.params do
    let ptyTerm ← elabType param.type
    let pident := mkIdent param.name
    addParam pident param.type
    let binder ← `(Lean.Parser.Term.funBinder| ($pident : $ptyTerm))
    paramBinders := paramBinders.push binder

  let bodyTerm ← elabStmtList funDef.body

  -- For pure functions, annotate the body with the declared return type to catch
  -- type errors early. For effectful functions (using `<-` binds), the body is
  -- monadic (e.g. `EffectM ε α`) which doesn't match the declared return type
  -- (`α`), so we omit the annotation and let Lean infer the monadic type.
  let ctx ← get
  let annotatedBody ←
    if ctx.hasEffectfulOps then
      pure bodyTerm
    else
      `(($bodyTerm : $retTyTerm))
  let mut result : Term := annotatedBody
  for binder in paramBinders.reverse do
    result ← `(fun $binder => $result)

  return result

end Meirei.Elaborator
