/-
  Contract Verification for mySum Function

  Contract: If mySum receives a list where all elements are non-negative (≥ 0),
  then the result is non-negative.
-/

import Meirei.Examples.Functions.Advanced
import Meirei.Examples.Verification.Common

-- =============================================================================
-- MAIN RESULT: mySum_nonnegative_contract
--
-- Shows that mySum preserves non-negativity:
-- If all input elements are ≥ 0, then the result is ≥ 0
-- =============================================================================

-- Helper lemmas for allNonNegative (used by foldl_add_nonneg below)
theorem allNonNegative_cons (x : Int) (xs : List Int) :
    allNonNegative (x :: xs) ↔ x ≥ 0 ∧ allNonNegative xs := by rfl

theorem allNonNegative_tail (x : Int) (xs : List Int) (h : allNonNegative (x :: xs)) :
    allNonNegative xs := h.2

theorem allNonNegative_head (x : Int) (xs : List Int) (h : allNonNegative (x :: xs)) :
    x ≥ 0 := h.1

-- Key lemma: foldl with addition and non-negative accumulator stays non-negative
theorem foldl_add_nonneg (l : List Int) (acc : Int)
    (hacc : acc ≥ 0) (hpos : allNonNegative l) :
    List.foldl (fun a b => a + b) acc l ≥ 0 := by
  induction l generalizing acc with
  | nil =>
    simp [List.foldl]
    exact hacc
  | cons x xs ih =>
    simp [List.foldl]
    have hx : x ≥ 0 := allNonNegative_head x xs hpos
    have hacc' : acc + x ≥ 0 := by omega
    have hpos' : allNonNegative xs := allNonNegative_tail x xs hpos
    exact ih (acc + x) hacc' hpos'

-- *** MAIN THEOREM ***
-- mySum preserves non-negativity
theorem mySum_nonnegative_contract (l : List Int)
    (hpos : allNonNegative l) :
    mySum l ≥ 0 := by
  unfold mySum
  simp [intSum]
  apply foldl_add_nonneg
  · omega
  · exact hpos

-- =============================================================================
-- EXAMPLES
-- =============================================================================

example : mySum [1, 2, 3] ≥ 0 := by
  apply mySum_nonnegative_contract
  simp [allNonNegative]

example : mySum [0, 0, 0] ≥ 0 := by
  apply mySum_nonnegative_contract
  simp [allNonNegative]

example : mySum [5, 0, 15] ≥ 0 := by
  apply mySum_nonnegative_contract
  simp [allNonNegative]

example : mySum [] ≥ 0 := by
  apply mySum_nonnegative_contract
  simp [allNonNegative]

#check mySum_nonnegative_contract
#print mySum
