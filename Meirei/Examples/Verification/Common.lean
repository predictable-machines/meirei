/-
  Common helper definitions shared across verification examples
-/

/-- Predicate asserting all elements in a list are non-negative -/
def allNonNegative : List Int → Prop
  | [] => True
  | x :: xs => x ≥ 0 ∧ allNonNegative xs
