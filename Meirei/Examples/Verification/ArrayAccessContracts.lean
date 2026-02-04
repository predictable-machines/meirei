/-
  Array Access Contracts for Effectful Operations

  This module defines contracts (axioms) that specify when array access
  operations succeed or fail, and what properties the results satisfy.

  Note: We use List as the underlying representation since Meirei works with
  lists, but name the operations "array" since they model imperative array access.
-/

import PredictableVerification.Examples.Functions.EffectMParameterized

open EffectMParameterized

-- ============================================================================
-- Array Access Contracts (using List as representation)
-- ============================================================================

-- Note: arrayGet is defined in EffectMParameterized.lean as:
--   axiom arrayGet : List α → Int → EffectM ArrayGetError α

-- Contract: arrayGet succeeds for valid indices
axiom arrayGet_inbounds (arr : List α) (idx : Int) :
    0 ≤ idx → idx < arr.length →
    ∃ (v : α), arrayGet arr idx = .ok v

-- Contract: arrayGet fails for invalid indices
axiom arrayGet_outofbounds (arr : List α) (idx : Int) :
    idx < 0 ∨ idx ≥ arr.length →
    ∃ (e : ArrayGetError), arrayGet arr idx = .error e

-- Contract: when arrayGet succeeds, it returns the actual value
axiom arrayGet_value [Inhabited α] (arr : List α) (idx : Int) :
    0 ≤ idx → idx < arr.length →
    arrayGet arr idx = .ok (arr[idx.toNat]!)

-- Contract: arrayGet result satisfies a property if all elements do
--
-- This axiom allows property transfer from arrays to their accessed elements:
--   - If EVERY element in the array satisfies property P
--   - And the index is valid (in bounds)
--   - Then the result of arrayGet also satisfies P
--
-- Example: If arr = [2, 4, 6] and P = "is even", then:
--   - All elements satisfy P (2, 4, 6 are all even)
--   - arrayGet arr 1 ⊧ P  (the result, 4, is even)
--
-- Example: If arr = [10, 20, 30] and P = (· ≥ 0), then:
--   - All elements are ≥ 0
--   - arrayGet arr idx ⊧ (· ≥ 0) for any valid idx
axiom arrayGet_preserves_property (arr : List Int) (idx : Int) (P : Int → Prop) :
    (∀ i : Nat, i < arr.length → P arr[i]!) →
    0 ≤ idx → idx < arr.length →
    arrayGet arr idx ⊧ P

-- Derived: arrayGet succeeds when in bounds
theorem arrayGet_succeeds_of_inbounds [Inhabited α] (arr : List α) (idx : Int)
    (h_lower : 0 ≤ idx) (h_upper : idx < arr.length) :
    succeeds (arrayGet arr idx) := by
  have h_val := arrayGet_value arr idx h_lower h_upper
  unfold succeeds
  simp [h_val]

-- ============================================================================
-- Example: Meirei Function with Array Access
-- ============================================================================

-- An effectful function that computes an offset (same error type as arrayGet for composability)
axiom computeOffset : Int → EffectM ArrayGetError Int

-- Contract: computeOffset always succeeds and returns a non-negative value
axiom computeOffset_succeeds (n : Int) : ∃ (v : Int), computeOffset n = .ok v
axiom computeOffset_nonneg (n : Int) (h : n ≥ 0) : computeOffset n ⊧ (· ≥ 0)

-- A function that gets an offset from an effectful call, computes the index, then accesses the array
-- This demonstrates chaining effectful operations with computed indices
noncomputable def getAndAdd := [Meirei|
  def getAndAdd(arr: [int], start: int, base: int) : int {
    offset <- computeOffset(start);
    elem <- arrayGet(arr, start + offset);
    return base + elem;
  }
]

-- Theorem: Array access succeeds when computed index is in bounds
-- Note: offset comes from computeOffset(start), so we need to quantify over it
theorem getAndAdd_safe (arr : List Int) (start base : Int) (offset : Int)
    (h_offset : computeOffset start = .ok offset)
    (h_lower : 0 ≤ start + offset) (h_upper : start + offset < arr.length) :
    succeeds (getAndAdd arr start base) := by
  simp only [getAndAdd]
  simp [h_offset, Bind.bind, Except.bind]
  have h_val := arrayGet_value arr (start + offset) h_lower h_upper
  simp [h_val, Pure.pure, Except.pure]
  unfold succeeds
  simp

-- Theorem: If access is safe and all elements are non-negative, result ≥ base
theorem getAndAdd_geq_base (arr : List Int) (start base : Int) (offset : Int)
    (h_offset : computeOffset start = .ok offset)
    (h_lower : 0 ≤ start + offset) (h_upper : start + offset < arr.length)
    (h_arr_nonneg : ∀ i : Nat, i < arr.length → arr[i]! ≥ 0) :
    getAndAdd arr start base ⊧ (· ≥ base) := by
  simp only [getAndAdd]
  simp [h_offset, Bind.bind, Except.bind]
  have h_val := arrayGet_value arr (start + offset) h_lower h_upper
  rw [h_val]
  simp only [satisfies, Pure.pure, Except.pure]
  have h_idx_nat : (start + offset).toNat < arr.length := by omega
  have h_elem_nonneg : arr[(start + offset).toNat]! ≥ 0 := h_arr_nonneg (start + offset).toNat h_idx_nat
  exact Int.le_add_of_nonneg_right h_elem_nonneg

-- Theorem: Postcondition - getAndAdd returns base + elem where elem is the array element
theorem getAndAdd_postcondition (arr : List Int) (start base : Int) (offset : Int)
    (h_offset : computeOffset start = .ok offset)
    (h_lower : 0 ≤ start + offset) (h_upper : start + offset < arr.length) :
    getAndAdd arr start base ⊧ (· = base + arr[(start + offset).toNat]!) := by
  simp only [getAndAdd]
  simp [h_offset, Bind.bind, Except.bind]
  have h_val := arrayGet_value arr (start + offset) h_lower h_upper
  simp only [satisfies, h_val, Pure.pure, Except.pure]
  have h_idx : (start + offset).toNat < arr.length := by omega
  congr 1
  simp only [getElem!_def, List.getElem?_eq_getElem h_idx, Option.getD_some]

-- ============================================================================
-- Partial Correctness with Effect Assumptions as Axioms
-- ============================================================================

-- Axiom: computeOffset returns a deterministic value based on input
-- This encodes the assumption that computeOffset(start) always returns the same offset
axiom computeOffset_value (start : Int) : Int

axiom computeOffset_returns (start : Int) :
    computeOffset start = .ok (computeOffset_value start)

-- Axiom: arrayGet returns the actual array element when it succeeds
-- (This is already captured by arrayGet_value, but we state it in partial form)
axiom arrayGet_partial (arr : List Int) (idx : Int) :
    arrayGet arr idx ⊧! (· = arr[idx.toNat]!)

-- Theorem: Partial correctness - IF getAndAdd succeeds, THEN result = base + elem
-- This version doesn't require proving effects succeed; it just assumes they do
theorem getAndAdd_postcondition_partial (arr : List Int) (start base : Int) :
    getAndAdd arr start base ⊧! (· = base + arr[(start + computeOffset_value start).toNat]!) := by
  simp only [getAndAdd, satisfiesPartial]
  simp only [computeOffset_returns, Bind.bind, Except.bind]
  cases h : arrayGet arr (start + computeOffset_value start) with
  | error _ => trivial
  | ok elem =>
    simp only [Pure.pure, Except.pure]
    -- When arrayGet succeeds, it returns the array element
    have h_partial := arrayGet_partial arr (start + computeOffset_value start)
    simp only [satisfiesPartial, h] at h_partial
    rw [h_partial]
