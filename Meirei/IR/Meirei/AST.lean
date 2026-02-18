/-
  Meirei Abstract Syntax Tree

  This module defines inductive types representing the Meirei imperative language.
  These types form an intermediate representation between surface syntax and
  elaborated Lean code.
-/

namespace Meirei.AST

/-- Meirei type representation. All types are named — there are no built-in
    primitive types. `Int`, `String`, etc. are just names that resolve to
    Lean types. Parameterized types use `app`, e.g. `List Int` is
    `app (named "List") (named "Int")`. Syntax sugar `[T]` and `T?` desugar
    to `app` with `List` and `Option` respectively. -/
inductive MeireiType where
  | named : Lean.Name → MeireiType
  | app : MeireiType → MeireiType → MeireiType
  deriving Repr, BEq, Inhabited

/-- Binary operators -/
inductive BinOp where
  | add  -- +
  | sub  -- -
  | mul  -- *
  | div  -- /
  | mod  -- %
  | gt   -- >
  | lt   -- <
  | ge   -- >=
  | le   -- <=
  | eq   -- ==
  | ne   -- !=
  | and_    -- &&
  | or_     -- ||
  | append  -- ++ (string concatenation)
  deriving Repr, BEq, Inhabited

/-- Unary operators -/
inductive UnaryOp where
  | not_ -- !
  deriving Repr, BEq, Inhabited

/-- Meirei expression representation -/
inductive MeireiExpr where
  | var : Lean.Name → MeireiExpr
  | intLit : Int → MeireiExpr
  | boolLit : Bool → MeireiExpr
  | stringLit : String → MeireiExpr
  | listLit : List MeireiExpr → MeireiExpr
  | binOp : BinOp → MeireiExpr → MeireiExpr → MeireiExpr
  | unaryOp : UnaryOp → MeireiExpr → MeireiExpr
  | call : Lean.Name → List MeireiExpr → MeireiExpr
  | fieldAccess : MeireiExpr → Lean.Name → MeireiExpr
  deriving Repr, Inhabited

/-- Meirei pattern for match arms -/
inductive MeireiPattern where
  | ctor : Lean.Name → List Lean.Name → MeireiPattern
  deriving Repr, BEq, Inhabited

/-- Meirei statement representation -/
inductive MeireiStmt where
  | varDecl : Lean.Name → MeireiType → MeireiExpr → MeireiStmt
  | assign : Lean.Name → MeireiExpr → MeireiStmt
  | ret : MeireiExpr → MeireiStmt
  | break_ : MeireiStmt
  | throw_ : MeireiExpr → MeireiStmt
  | forLoop : Lean.Name → MeireiExpr → List MeireiStmt → MeireiStmt
  | ifThen : MeireiExpr → List MeireiStmt → MeireiStmt
  | ifThenElse : MeireiExpr → List MeireiStmt → List MeireiStmt → MeireiStmt
  | block : List MeireiStmt → MeireiStmt
  | effectCall : Lean.Name → List MeireiExpr → MeireiStmt
  | effectBind : Lean.Name → Lean.Name → List MeireiExpr → MeireiStmt
  | match_ : MeireiExpr → List (MeireiPattern × List MeireiStmt) → MeireiStmt
  | whileLoop : MeireiExpr → List MeireiStmt → Option MeireiExpr → MeireiStmt
  deriving Repr, Inhabited

/-- Convenience alias for match arms -/
abbrev MatchArm := MeireiPattern × List MeireiStmt

def MatchArm.pattern (arm : MatchArm) : MeireiPattern := arm.1
def MatchArm.body (arm : MatchArm) : List MeireiStmt := arm.2
def MatchArm.mk (pattern : MeireiPattern) (body : List MeireiStmt) : MatchArm := (pattern, body)

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

/-- A field definition used in structs and enum constructors -/
structure MeireiFieldDef where
  name : Lean.Name
  type : MeireiType
  deriving Repr, Inhabited

/-- An enum constructor with named fields -/
structure MeireiEnumCtor where
  name : Lean.Name
  fields : List MeireiFieldDef
  deriving Repr, Inhabited

/-- Meirei struct definition -/
structure MeireiStructDef where
  name : Lean.Name
  fields : List MeireiFieldDef
  deriving Repr, Inhabited

/-- Meirei enum definition -/
structure MeireiEnumDef where
  name : Lean.Name
  ctors : List MeireiEnumCtor
  deriving Repr, Inhabited

end Meirei.AST
