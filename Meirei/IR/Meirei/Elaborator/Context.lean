/-
  Elaboration Context Management

  This module defines the core data structures for tracking variables
  and control flow state during elaboration, plus functions for managing
  the elaboration context (adding variables, updating versions, etc).
-/

import Lean
import Meirei.IR.Meirei.AST

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

open Meirei.AST

-- =============================================================================
-- Data Structures
-- =============================================================================

/-- Information about a variable in scope -/
structure VarInfo where
  name : Name
  type : MeireiType
  currentVersion : Nat  -- For SSA-style naming (x becomes x_0, x_1, ...)
  origIdent : Option Ident := none  -- Store original identifier for hygiene (parameters)
  deriving Repr, Inhabited

/-- Elaboration context tracking variables and control flow state -/
structure ElabContext where
  vars : Std.HashMap Name VarInfo := {}
  loopDepth : Nat := 0
  inLoop : Bool := false
  inEarlyReturnLoop : Bool := false  -- Are we in a loop with early return?
  inBreakLoop : Bool := false  -- Are we in a loop with break?
  pendingOptionExtraction : Option (Ident × Term) := none  -- (resultIdent, defaultValue) for Option extraction
  pendingMixedReturn : Option (Ident × Ident) := none  -- (optionIdent, accumIdent) for mixed return + accumulation
  hasEffectfulOps : Bool := false  -- Has this function seen any effectful operations?
  inExceptFunction : Bool := false  -- Is the current function returning Except(E, T)?
  exceptErrorType : Option MeireiType := none  -- The error type E when in an Except function
  deriving Inhabited

/-- Elaboration monad -/
abbrev ElabM := StateT ElabContext MacroM

-- =============================================================================
-- Context Management Functions
-- =============================================================================

/-- Add a new variable to context -/
def addVar (name : Name) (type : MeireiType) : ElabM Ident := do
  let ctx ← get
  let info : VarInfo := { name, type, currentVersion := 0 }
  set { ctx with vars := ctx.vars.insert name info }
  return mkIdent (name.appendAfter "_0")

/-- Add a parameter to context (uses original name, not versioned) -/
def addParam (ident : Ident) (type : MeireiType) : ElabM Unit := do
  let ctx ← get
  let info : VarInfo := { name := ident.getId, type, currentVersion := 0, origIdent := some ident }
  set { ctx with vars := ctx.vars.insert ident.getId info }

/-- Update a variable (create new version) -/
def updateVar (name : Name) : ElabM Ident := do
  let ctx ← get
  match ctx.vars[name]? with
  | none => throw <| Macro.Exception.error (← getRef) s!"Variable {name} not found"
  | some info =>
    let newVersion := info.currentVersion + 1
    let newInfo : VarInfo := { info with currentVersion := newVersion }
    set { ctx with vars := ctx.vars.insert name newInfo }
    return mkIdent (name.appendAfter s!"_{newVersion}")

/-- Get current version of a variable -/
def getVar (name : Name) : ElabM Ident := do
  let ctx ← get
  match ctx.vars[name]? with
  | none => throw <| Macro.Exception.error (← getRef) s!"Variable {name} not found"
  | some info =>
    return mkIdent (name.appendAfter s!"_{info.currentVersion}")

end Meirei.Elaborator
