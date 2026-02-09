/-
  Meirei Syntax Parser

  This module transforms Lean syntax (TSyntax) into the Meirei AST.
  It performs a mechanical translation from surface syntax to AST nodes.
-/

import Lean
import PredictableVerification.IR.Meirei.Syntax
import PredictableVerification.IR.Meirei.AST

open Lean

namespace Meirei.Parser

open Meirei.AST

/-- Parse a type syntax to MeireiType -/
partial def parseType (stx : TSyntax `imp_type) : MacroM MeireiType := do
  match stx with
  | `(imp_type| int) => return MeireiType.int
  | `(imp_type| [ $ty:imp_type ]) => do
    let inner ← parseType ty
    return MeireiType.list inner
  | _ => Macro.throwError s!"Unsupported type syntax: {stx}"

/-- Parse an expression syntax to MeireiExpr -/
partial def parseExpr (stx : TSyntax `imp_expr) : MacroM MeireiExpr := do
  match stx with
  | `(imp_expr| $n:num) =>
    return MeireiExpr.intLit n.getNat

  | `(imp_expr| - $n:num) =>
    return MeireiExpr.intLit (- n.getNat)

  | `(imp_expr| $x:ident) =>
    return MeireiExpr.var x.getId

  | `(imp_expr| $a:imp_expr + $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.add a' b'

  | `(imp_expr| $a:imp_expr - $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.sub a' b'

  | `(imp_expr| $a:imp_expr * $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.mul a' b'

  | `(imp_expr| $a:imp_expr / $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.div a' b'

  | `(imp_expr| $a:imp_expr > $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.gt a' b'

  | `(imp_expr| $a:imp_expr < $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.lt a' b'

  | `(imp_expr| $a:imp_expr == $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.eq a' b'

  | `(imp_expr| $f:ident ( $args,* )) => do
    let args' ← args.getElems.toList.mapM parseExpr
    return MeireiExpr.call f.getId args'

  | `(imp_expr| ( $e:imp_expr )) =>
    parseExpr e

  | _ => Macro.throwError s!"Unsupported expression syntax: {stx}"

/-- Parse a statement syntax to MeireiStmt -/
partial def parseStmt (stx : TSyntax `imp_stmt) : MacroM MeireiStmt := do
  match stx with
  | `(imp_stmt| var $x:ident : $ty:imp_type = $init:imp_expr ;) => do
    let ty' ← parseType ty
    let init' ← parseExpr init
    return MeireiStmt.varDecl x.getId ty' init'

  | `(imp_stmt| $x:ident = $rhs:imp_expr ;) => do
    let rhs' ← parseExpr rhs
    return MeireiStmt.assign x.getId rhs'

  | `(imp_stmt| return $e:imp_expr ;) => do
    let e' ← parseExpr e
    return MeireiStmt.ret e'

  | `(imp_stmt| break ;) =>
    return MeireiStmt.break_

  | `(imp_stmt| for $x:ident in $coll:imp_expr { $stmts* }) => do
    let coll' ← parseExpr coll
    let stmts' ← stmts.toList.mapM parseStmt
    return MeireiStmt.forLoop x.getId coll' stmts'

  | `(imp_stmt| if ( $cond:imp_expr ) { $stmts* }) => do
    let cond' ← parseExpr cond
    let stmts' ← stmts.toList.mapM parseStmt
    return MeireiStmt.ifThen cond' stmts'

  | `(imp_stmt| if ( $cond:imp_expr ) { $thenStmts* } else { $elseStmts* }) => do
    let cond' ← parseExpr cond
    let thenStmts' ← thenStmts.toList.mapM parseStmt
    let elseStmts' ← elseStmts.toList.mapM parseStmt
    return MeireiStmt.ifThenElse cond' thenStmts' elseStmts'

  | `(imp_stmt| { $stmts* }) => do
    let stmts' ← stmts.toList.mapM parseStmt
    return MeireiStmt.block stmts'

  | `(imp_stmt| $f:ident ( $args,* ) ;) => do
    let args' ← args.getElems.toList.mapM parseExpr
    return MeireiStmt.effectCall f.getId args'

  | `(imp_stmt| $y:ident <- $f:ident ( $args,* ) ;) => do
    let args' ← args.getElems.toList.mapM parseExpr
    return MeireiStmt.effectBind y.getId f.getId args'

  | _ => Macro.throwError s!"Unsupported statement syntax: {stx}"

/-- Parse a parameter syntax to MeireiParam -/
def parseParam (stx : TSyntax `imp_param) : MacroM MeireiParam := do
  match stx with
  | `(imp_param| $pname:ident : $pty:imp_type) => do
    let pty' ← parseType pty
    return { name := pname.getId, type := pty' }
  | _ => Macro.throwError s!"Invalid parameter syntax: {stx}"

/-- Parse a function definition syntax to MeireiFunDef -/
def parseFunDef (stx : TSyntax `imp_fundef) : MacroM MeireiFunDef := do
  match stx with
  | `(imp_fundef| def $name:ident ( $params,* ) : $retTy:imp_type { $stmts* }) => do
    let params' ← params.getElems.toList.mapM parseParam
    let retTy' ← parseType retTy
    let body' ← stmts.toList.mapM parseStmt
    return {
      name := name.getId,
      params := params',
      returnType := retTy',
      body := body'
    }
  | _ => Macro.throwError s!"Invalid function definition syntax: {stx}"

end Meirei.Parser
