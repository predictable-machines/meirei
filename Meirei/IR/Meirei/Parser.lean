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

/-- Resolve a type name that may have trailing `?` characters (e.g. `Int?`, `Shape??`).
    The tokenizer merges `T?` into a single ident, so we strip trailing `?` here.
    Type names must start with an uppercase letter. -/
private def resolveTypeName (name : String) : MacroM MeireiType := do
  let numQuestions := name.toList.reverse.takeWhile (· == '?') |>.length
  let baseName := (name.dropEnd numQuestions).toString
  match baseName.toList.head? with
  | some c =>
    if !c.isUpper then
      Macro.throwError s!"Type names must start with an uppercase letter, got '{baseName}'"
  | none => Macro.throwError s!"Empty type name"
  let baseType := MeireiType.named (Name.mkSimple baseName)
  let rec wrap (n : Nat) (ty : MeireiType) : MeireiType :=
    match n with
    | 0 => ty
    | n + 1 => wrap n (MeireiType.app (MeireiType.named `Option) ty)
  return wrap numQuestions baseType

/-- Parse a type syntax to MeireiType -/
partial def parseType (stx : TSyntax `imp_type) : MacroM MeireiType := do
  match stx with
  | `(imp_type| [ $ty:imp_type ]) => do
    let inner ← parseType ty
    return MeireiType.app (MeireiType.named `List) inner
  | `(imp_type| $ty:imp_type ?) => do
    let inner ← parseType ty
    return MeireiType.app (MeireiType.named `Option) inner
  | `(imp_type| $n:ident ( $args,* )) => do
    let argsList := args.getElems.toList
    if argsList.isEmpty then
      Macro.throwError "Type application requires at least one argument"
    let baseName := n.getId.toString
    match baseName.toList.head? with
    | some c => if !c.isUpper then Macro.throwError s!"Type names must start with uppercase, got '{baseName}'"
    | none => Macro.throwError "Empty type name"
    let mut result := MeireiType.named (Name.mkSimple baseName)
    for arg in argsList do
      let argTy ← parseType arg
      result := MeireiType.app result argTy
    return result
  | `(imp_type| $n:ident) => resolveTypeName n.getId.toString
  | _ => Macro.throwError s!"Unsupported type syntax: {stx}"

/-- Try to extract a string literal from a syntax node, navigating wrapper nodes. -/
private def extractStrLit (stx : Syntax) : Option String :=
  -- Direct match
  stx.isStrLit? <|>
  -- One level deep (str wraps strLit atom)
  stx[0]?.bind (·.isStrLit?) <|>
  -- Choice node from parser ambiguity: check each alternative
  (if stx.getKind == choiceKind then
    stx.getArgs.findSome? fun alt =>
      alt.isStrLit? <|> alt[0]?.bind (·.isStrLit?)
  else none)

mutual

/-- Parse a function call argument (expression or string literal) -/
partial def parseArg (stx : TSyntax `imp_arg) : MacroM MeireiExpr := do
  -- Try string extraction first (handles choice nodes from ambiguity)
  if let some s := extractStrLit stx.raw then
    return MeireiExpr.stringLit s
  -- Otherwise parse as expression
  match stx with
  | `(imp_arg| $e:imp_expr) => parseExpr e
  | _ => Macro.throwError s!"Unsupported argument syntax: {stx}"

/-- Parse an expression syntax to MeireiExpr -/
partial def parseExpr (stx : TSyntax `imp_expr) : MacroM MeireiExpr := do
  match stx with
  | `(imp_expr| $n:num) =>
    return MeireiExpr.intLit n.getNat

  | `(imp_expr| - $n:num) =>
    return MeireiExpr.intLit (- n.getNat)

  | `(imp_expr| $x:ident) =>
    let name := x.getId
    if name == `true then return MeireiExpr.boolLit true
    else if name == `false then return MeireiExpr.boolLit false
    else return MeireiExpr.var name

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

  | `(imp_expr| $a:imp_expr % $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.mod a' b'

  | `(imp_expr| $a:imp_expr > $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.gt a' b'

  | `(imp_expr| $a:imp_expr < $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.lt a' b'

  | `(imp_expr| $a:imp_expr >= $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.ge a' b'

  | `(imp_expr| $a:imp_expr <= $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.le a' b'

  | `(imp_expr| $a:imp_expr == $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.eq a' b'

  | `(imp_expr| $a:imp_expr != $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.ne a' b'

  | `(imp_expr| $a:imp_expr && $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.and_ a' b'

  | `(imp_expr| $a:imp_expr || $b:imp_expr) => do
    let a' ← parseExpr a
    let b' ← parseExpr b
    return MeireiExpr.binOp BinOp.or_ a' b'

  | `(imp_expr| ! $a:imp_expr) => do
    let a' ← parseExpr a
    return MeireiExpr.unaryOp UnaryOp.not_ a'

  | `(imp_expr| $f:ident ( $args,* )) => do
    let args' ← args.getElems.toList.mapM parseArg
    return MeireiExpr.call f.getId args'

  | `(imp_expr| ( $e:imp_expr )) =>
    parseExpr e

  | `(imp_expr| $obj:imp_expr . $field:ident) => do
    let obj' ← parseExpr obj
    return MeireiExpr.fieldAccess obj' field.getId

  | other =>
    -- `syntax:max str : imp_expr` wraps the strLit in an imp_expr node.
    -- Navigate one level to the `str` child where `isStrLit?` works.
    if let some s := other.raw[0]?.bind Syntax.isStrLit? then
      return MeireiExpr.stringLit s
    Macro.throwError s!"Unsupported expression syntax: {other}"

/-- Parse a match arm syntax to a MatchArm -/
partial def parseMatchArm (stx : TSyntax `imp_match_arm) : MacroM MatchArm := do
  match stx with
  | `(imp_match_arm| case $ctorName:ident ( $bindings,* ) { $stmts* }) => do
    let bindings' := bindings.getElems.toList.map (·.getId)
    let body' ← stmts.toList.mapM parseStmt
    return MatchArm.mk (MeireiPattern.ctor ctorName.getId bindings') body'
  | _ => Macro.throwError s!"Invalid match arm syntax: {stx}"

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

  | `(imp_stmt| throw $e:imp_expr ;) => do
    let e' ← parseExpr e
    return MeireiStmt.throw_ e'

  | `(imp_stmt| for $x:ident in $coll:imp_expr { $stmts* }) => do
    let coll' ← parseExpr coll
    let stmts' ← stmts.toList.mapM parseStmt
    return MeireiStmt.forLoop x.getId coll' stmts'

  | `(imp_stmt| while ( $cond:imp_expr ) $[decreasing ( $decr:imp_expr )]? { $stmts* }) => do
    let cond' ← parseExpr cond
    let decr' ← match decr with
      | some d => do pure (some (← parseExpr d))
      | none => pure none
    let stmts' ← stmts.toList.mapM parseStmt
    return MeireiStmt.whileLoop cond' stmts' decr'

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
    let args' ← args.getElems.toList.mapM parseArg
    return MeireiStmt.effectCall f.getId args'

  | `(imp_stmt| $y:ident <- $f:ident ( $args,* ) ;) => do
    let args' ← args.getElems.toList.mapM parseArg
    return MeireiStmt.effectBind y.getId f.getId args'

  | `(imp_stmt| match $scrutinee:imp_expr { $arms* }) => do
    let scrutinee' ← parseExpr scrutinee
    let arms' ← arms.toList.mapM parseMatchArm
    return MeireiStmt.match_ scrutinee' arms'

  | _ => Macro.throwError s!"Unsupported statement syntax: {stx}"

end

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

/-- Parse a field definition -/
def parseFieldDef (stx : TSyntax `imp_field_def) : MacroM MeireiFieldDef := do
  match stx with
  | `(imp_field_def| $name:ident : $ty:imp_type) => do
    let ty' ← parseType ty
    return { name := name.getId, type := ty' }
  | _ => Macro.throwError s!"Invalid field definition syntax: {stx}"

/-- Parse an enum constructor -/
def parseEnumCtor (stx : TSyntax `imp_enum_ctor) : MacroM MeireiEnumCtor := do
  match stx with
  | `(imp_enum_ctor| $name:ident ( $fields,* )) => do
    let fields' ← fields.getElems.toList.mapM parseFieldDef
    return { name := name.getId, fields := fields' }
  | _ => Macro.throwError s!"Invalid enum constructor syntax: {stx}"

/-- Parse a struct definition -/
def parseStructDef (stx : TSyntax `imp_struct_def) : MacroM MeireiStructDef := do
  match stx with
  | `(imp_struct_def| struct $name:ident { $fields,* }) => do
    let fields' ← fields.getElems.toList.mapM parseFieldDef
    return { name := name.getId, fields := fields' }
  | _ => Macro.throwError s!"Invalid struct definition syntax: {stx}"

/-- Parse an enum definition -/
def parseEnumDef (stx : TSyntax `imp_enum_def) : MacroM MeireiEnumDef := do
  match stx with
  | `(imp_enum_def| enum $name:ident { $ctors,* }) => do
    let ctors' ← ctors.getElems.toList.mapM parseEnumCtor
    return { name := name.getId, ctors := ctors' }
  | _ => Macro.throwError s!"Invalid enum definition syntax: {stx}"

end Meirei.Parser
