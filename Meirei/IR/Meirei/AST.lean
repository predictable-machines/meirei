/-
  Meirei Abstract Syntax Tree

  This module defines inductive types representing the Meirei imperative language.
  These types form an intermediate representation between surface syntax and
  elaborated Lean code.
-/

namespace Meirei.AST

/-- Meirei type representation -/
inductive MeireiType where
  | int : MeireiType
  | list : MeireiType → MeireiType
  deriving Repr, BEq, Inhabited

/-- Binary operators -/
inductive BinOp where
  | add  -- +
  | sub  -- -
  | mul  -- *
  | div  -- /
  | gt   -- >
  | lt   -- <
  | eq   -- ==
  deriving Repr, BEq, Inhabited

/-- Meirei expression representation -/
inductive MeireiExpr where
  | var : Lean.Name → MeireiExpr
  | intLit : Int → MeireiExpr
  | binOp : BinOp → MeireiExpr → MeireiExpr → MeireiExpr
  | call : Lean.Name → List MeireiExpr → MeireiExpr
  deriving Repr, Inhabited

/-- Meirei statement representation -/
inductive MeireiStmt where
  | varDecl : Lean.Name → MeireiType → MeireiExpr → MeireiStmt
  | assign : Lean.Name → MeireiExpr → MeireiStmt
  | ret : MeireiExpr → MeireiStmt
  | break_ : MeireiStmt
  | forLoop : Lean.Name → MeireiExpr → List MeireiStmt → MeireiStmt
  | ifThen : MeireiExpr → List MeireiStmt → MeireiStmt
  | ifThenElse : MeireiExpr → List MeireiStmt → List MeireiStmt → MeireiStmt
  | block : List MeireiStmt → MeireiStmt
  | effectCall : Lean.Name → List MeireiExpr → MeireiStmt
  | effectBind : Lean.Name → Lean.Name → List MeireiExpr → MeireiStmt
  deriving Repr, Inhabited

/-- Meirei parameter representation -/
structure MeireiParam where
  name : Lean.Name
  type : MeireiType
  deriving Repr, Inhabited

/-- Meirei function definition representation -/
structure MeireiFunDef where
  name : Lean.Name
  params : List MeireiParam
  returnType : MeireiType
  body : List MeireiStmt
  deriving Repr, Inhabited

end Meirei.AST
