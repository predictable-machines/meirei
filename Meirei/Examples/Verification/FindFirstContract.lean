/-
  Contract Verification for findFirstGreaterThan10 Function

  Contract: The result of findFirstGreaterThan10 is either 0 (indicating no element
  greater than 10 was found) or a value strictly greater than 10 (the first such element).

  This property captures the correctness of the search: we never return a value
  between 1 and 10 inclusive.

  This was completely proven by Claude Code from a single prompt:
  "Come up with some interesting property about findFirstGreaterThan10,
  and then create a contract module for it, then prove that the function satisfies the property."
-/

import PredictableVerification.Examples.Functions.EarlyExit

-- =============================================================================
-- MAIN RESULT: findFirstGreaterThan10_contract
--
-- Shows that the function returns either 0 or a value > 10
-- (never returns a value between 1 and 10 inclusive)
-- =============================================================================

-- Supporting lemma: the foldl maintains the invariant that any value in the Option is > 10
theorem foldl_option_gt_ten (l : List Int) (acc : Option Int)
    (hacc : acc = none ∨ ∃ v, acc = some v ∧ v > 10) :
    let result := List.foldl (fun acc x =>
      if acc.isSome = true then acc else if x > 10 then some x else none
    ) acc l
    result = none ∨ ∃ v, result = some v ∧ v > 10 := by
  induction l generalizing acc with
  | nil =>
    simp [List.foldl]
    exact hacc
  | cons y ys ih =>
    simp only [List.foldl]
    cases hacc with
    | inl h_none =>
      rw [h_none]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      split
      · -- y > 10
        rename_i hy
        apply ih
        right
        exact ⟨y, rfl, hy⟩
      · -- y ≤ 10
        apply ih
        left
        rfl
    | inr h_some =>
      obtain ⟨v, hv_eq, hv_gt⟩ := h_some
      rw [hv_eq]
      simp only [Option.isSome_some, ↓reduceIte]
      apply ih
      right
      exists v

-- Key lemma: connecting foldl result to getD result
theorem foldl_getD_property (nums : List Int) :
    let foldResult := List.foldl (fun acc x =>
      if acc.isSome = true then acc else if x > 10 then some x else none
    ) none nums
    foldResult.getD 0 = 0 ∨ foldResult.getD 0 > 10 := by
  have h_inv := foldl_option_gt_ten nums none (Or.inl rfl)
  cases h_inv with
  | inl h_none =>
    left
    simp only [h_none, Option.getD_none]
  | inr h_some =>
    obtain ⟨v, hv_eq, hv_gt⟩ := h_some
    right
    simp only [hv_eq, Option.getD_some]
    exact hv_gt

-- *** MAIN THEOREM ***
-- findFirstGreaterThan10 returns either 0 or a value > 10
theorem findFirstGreaterThan10_contract (nums : List Int) :
    findFirstGreaterThan10 nums = 0 ∨ findFirstGreaterThan10 nums > 10 := by
  show (List.foldl (fun acc x =>
    if acc.isSome = true then acc else if x > 10 then some x else none
  ) none nums).getD 0 = 0 ∨ (List.foldl (fun acc x =>
    if acc.isSome = true then acc else if x > 10 then some x else none
  ) none nums).getD 0 > 10
  exact foldl_getD_property nums

-- =============================================================================
-- ADDITIONAL HELPERS (not used by main theorem)
-- =============================================================================

-- Helper lemma about Option.getD
theorem getD_zero_cases (opt : Option Int) :
    opt.getD 0 = 0 ∨ ∃ v, opt = some v ∧ opt.getD 0 = v := by
  cases opt with
  | none => left; rfl
  | some v => right; exists v

-- =============================================================================
-- EXAMPLES
-- =============================================================================

example : findFirstGreaterThan10 [1, 5, 3, 15, 20] = 15 := by rfl
example : findFirstGreaterThan10 [1, 5, 3, 15, 20] > 10 := by decide
example : findFirstGreaterThan10 [1, 2, 3] = 0 := by rfl
example : findFirstGreaterThan10 [20, 30, 5] = 20 := by rfl
example : findFirstGreaterThan10 [20, 30, 5] > 10 := by decide
example : findFirstGreaterThan10 [] = 0 := by rfl
example : findFirstGreaterThan10 [11] > 10 := by decide
example : findFirstGreaterThan10 [10, 11, 12] > 10 := by decide
example : findFirstGreaterThan10 [5, 8, 10] = 0 := by rfl

-- Verify using the contract
example : findFirstGreaterThan10 [1, 2, 3] = 0 ∨ findFirstGreaterThan10 [1, 2, 3] > 10 := by
  apply findFirstGreaterThan10_contract

#check findFirstGreaterThan10_contract
#print findFirstGreaterThan10
