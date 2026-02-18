/-
  Meirei AST Analysis

  This module provides analysis functions that operate on the Meirei AST.
  These include control flow detection, effectful operation detection,
  and variable modification tracking.
-/

import PredictableVerification.IR.Meirei.AST

open Lean

namespace Meirei.Analysis

open Meirei.AST

/-- Control flow type detected in a statement -/
inductive ControlFlowType where
  | none
  | hasReturn
  | hasBreak
  deriving Repr, BEq, Inhabited

mutual

/-- Detect control flow type in a single statement -/
partial def detectControlFlow (stmt : MeireiStmt) : ControlFlowType :=
  match stmt with
  | MeireiStmt.ret _ => ControlFlowType.hasReturn
  | MeireiStmt.throw_ _ => ControlFlowType.hasReturn
  | MeireiStmt.break_ => ControlFlowType.hasBreak
  | MeireiStmt.ifThen _ stmts => detectControlFlowInList stmts
  | MeireiStmt.ifThenElse _ thenStmts elseStmts =>
    let thenCf := detectControlFlowInList thenStmts
    if thenCf != ControlFlowType.none then thenCf
    else detectControlFlowInList elseStmts
  | MeireiStmt.block stmts => detectControlFlowInList stmts
  | MeireiStmt.forLoop _ _ stmts => detectControlFlowInList stmts
  | MeireiStmt.whileLoop _ stmts _ => detectControlFlowInList stmts
  | MeireiStmt.match_ _ arms =>
    arms.foldl (fun acc (_, body) =>
      if acc != ControlFlowType.none then acc
      else detectControlFlowInList body
    ) ControlFlowType.none
  | _ => ControlFlowType.none

/-- Detect control flow type in a list of statements -/
partial def detectControlFlowInList (stmts : List MeireiStmt) : ControlFlowType :=
  stmts.foldl (fun acc stmt =>
    if acc != ControlFlowType.none then acc
    else detectControlFlow stmt
  ) ControlFlowType.none

end

/-- Detect if a statement contains effectful operations -/
partial def detectEffectfulOps (stmt : MeireiStmt) : Bool :=
  match stmt with
  | MeireiStmt.effectCall _ _ => true
  | MeireiStmt.effectBind _ _ _ => true
  | MeireiStmt.ifThen _ stmts => stmts.any detectEffectfulOps
  | MeireiStmt.ifThenElse _ thenStmts elseStmts =>
    thenStmts.any detectEffectfulOps || elseStmts.any detectEffectfulOps
  | MeireiStmt.block stmts => stmts.any detectEffectfulOps
  | MeireiStmt.forLoop _ _ stmts => stmts.any detectEffectfulOps
  | MeireiStmt.whileLoop _ stmts _ => stmts.any detectEffectfulOps
  | MeireiStmt.match_ _ arms => arms.any (fun (_, body) => body.any detectEffectfulOps)
  | _ => false

/-- Detect effectful operations in a list of statements -/
def detectEffectfulOpsInList (stmts : List MeireiStmt) : Bool :=
  stmts.any detectEffectfulOps

/-- Detect if a statement contains throw operations -/
partial def detectThrowOps (stmt : MeireiStmt) : Bool :=
  match stmt with
  | MeireiStmt.throw_ _ => true
  | MeireiStmt.ifThen _ stmts => stmts.any detectThrowOps
  | MeireiStmt.ifThenElse _ t e => t.any detectThrowOps || e.any detectThrowOps
  | MeireiStmt.block stmts => stmts.any detectThrowOps
  | MeireiStmt.forLoop _ _ stmts => stmts.any detectThrowOps
  | MeireiStmt.whileLoop _ stmts _ => stmts.any detectThrowOps
  | MeireiStmt.match_ _ arms => arms.any (fun (_, body) => body.any detectThrowOps)
  | _ => false

/-- Detect throw operations in a list of statements -/
def detectThrowOpsInList (stmts : List MeireiStmt) : Bool :=
  stmts.any detectThrowOps

mutual

/-- Collect all variables declared in statements -/
partial def collectDeclaredVars (stmt : MeireiStmt) : List Name :=
  match stmt with
  | MeireiStmt.varDecl name _ _ => [name]
  | MeireiStmt.ifThen _ stmts => collectDeclaredVarsInList stmts
  | MeireiStmt.ifThenElse _ thenStmts elseStmts =>
    collectDeclaredVarsInList thenStmts ++ collectDeclaredVarsInList elseStmts
  | MeireiStmt.block stmts => collectDeclaredVarsInList stmts
  | MeireiStmt.forLoop loopVar _ stmts => loopVar :: collectDeclaredVarsInList stmts
  | MeireiStmt.whileLoop _ stmts _ => collectDeclaredVarsInList stmts
  | MeireiStmt.match_ _ arms =>
    arms.foldl (fun acc (_, body) => acc ++ collectDeclaredVarsInList body) []
  | _ => []

/-- Collect all variables declared in a list of statements -/
partial def collectDeclaredVarsInList (stmts : List MeireiStmt) : List Name :=
  stmts.foldl (fun acc stmt => acc ++ collectDeclaredVars stmt) []

end

mutual

/-- Collect all variables assigned in statements (not declarations) -/
partial def collectAssignedVars (stmt : MeireiStmt) : List Name :=
  match stmt with
  | MeireiStmt.assign name _ => [name]
  | MeireiStmt.ifThen _ stmts => collectAssignedVarsInList stmts
  | MeireiStmt.ifThenElse _ thenStmts elseStmts =>
    collectAssignedVarsInList thenStmts ++ collectAssignedVarsInList elseStmts
  | MeireiStmt.block stmts => collectAssignedVarsInList stmts
  | MeireiStmt.forLoop _ _ stmts => collectAssignedVarsInList stmts
  | MeireiStmt.whileLoop _ stmts _ => collectAssignedVarsInList stmts
  | MeireiStmt.match_ _ arms =>
    arms.foldl (fun acc (_, body) => acc ++ collectAssignedVarsInList body) []
  | _ => []

/-- Collect all variables assigned in a list of statements -/
partial def collectAssignedVarsInList (stmts : List MeireiStmt) : List Name :=
  stmts.foldl (fun acc stmt => acc ++ collectAssignedVars stmt) []

end

/-- Find variables that are modified in a list of statements.
    A variable is modified if it's assigned to and exists in the given scope. -/
def findModifiedVars (stmts : List MeireiStmt) (existingVars : List Name) : List Name :=
  let assigned := collectAssignedVarsInList stmts
  let filtered := assigned.filter (existingVars.contains ·)
  filtered.eraseDups

mutual

/-- Collect all variables referenced in an expression -/
partial def collectExprVars (expr : MeireiExpr) : List Name :=
  match expr with
  | MeireiExpr.var name => [name]
  | MeireiExpr.intLit _ => []
  | MeireiExpr.boolLit _ => []
  | MeireiExpr.stringLit _ => []
  | MeireiExpr.listLit elems => collectExprVarsInList elems
  | MeireiExpr.binOp _ lhs rhs => collectExprVars lhs ++ collectExprVars rhs
  | MeireiExpr.unaryOp _ operand => collectExprVars operand
  | MeireiExpr.call _ args => collectExprVarsInList args
  | MeireiExpr.fieldAccess obj _ => collectExprVars obj

/-- Collect all variables referenced in a list of expressions -/
partial def collectExprVarsInList (exprs : List MeireiExpr) : List Name :=
  exprs.foldl (fun acc expr => acc ++ collectExprVars expr) []

end

/-- Check if a type is Except(E, T), returning (E, T) if so -/
def isExceptReturnType (ty : MeireiType) : Option (MeireiType × MeireiType) :=
  match ty with
  | MeireiType.app (MeireiType.app (MeireiType.named name) errTy) valTy =>
    if name == `Except then some (errTy, valTy) else none
  | _ => none

end Meirei.Analysis
