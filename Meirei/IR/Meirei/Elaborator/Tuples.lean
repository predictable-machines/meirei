/-
  Tuple Helpers

  This module provides utilities for building tuple syntax from terms
  and identifiers. These are used when loops modify multiple variables
  simultaneously.
-/

import Lean

open Lean Lean.Elab Lean.Meta

namespace Meirei.Elaborator

-- =============================================================================
-- Tuple Building Functions
-- =============================================================================

/-- Build a tuple from terms -/
def buildTupleFromTerms (terms : Array Term) : MacroM Term := do
  if terms.isEmpty then
    `(())
  else if terms.size == 1 then
    return terms[0]!
  else if terms.size == 2 then
    `(($(terms[0]!), $(terms[1]!)))
  else
    -- Build nested tuple: (a, (b, (c, ...)))
    let rec build (idx : Nat) : MacroM Term := do
      if idx >= terms.size - 1 then
        return terms[terms.size - 1]!
      else
        let rest ← build (idx + 1)
        `(($(terms[idx]!), $rest))
    build 0

/-- Build a pattern tuple from identifiers -/
def buildPatternTuple (idents : Array Ident) : MacroM Term := do
  if idents.isEmpty then
    `(_)
  else if idents.size == 1 then
    return idents[0]!
  else if idents.size == 2 then
    `(($(idents[0]!), $(idents[1]!)))
  else
    -- Build nested pattern: (a, (b, (c, ...)))
    let rec build (idx : Nat) : MacroM Term := do
      if idx >= idents.size - 1 then
        return idents[idents.size - 1]!
      else
        let rest ← build (idx + 1)
        `(($(idents[idx]!), $rest))
    build 0

end Meirei.Elaborator
