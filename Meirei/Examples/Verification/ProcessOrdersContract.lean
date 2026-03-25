/-
  Contract Verification for processOrders Function

  This file proves functional correctness properties about order processing.
-/

import Meirei.Examples.Functions.Effectful
import Meirei.Examples.Verification.Common

open Effectful

-- =============================================================================
-- EFFECT SPECIFICATIONS
-- =============================================================================

/-- The discount threshold is always non-negative -/
axiom getDiscountThreshold_nonneg : getDiscountThreshold () ⊧ (· ≥ 0)

/-- The discount multiplier is always at least 1 (no reduction below original) -/
axiom getDiscountMultiplier_pos : getDiscountMultiplier () ⊧ (· ≥ 1)

-- =============================================================================
-- HELPER DEFINITIONS
-- =============================================================================

-- Helper lemmas
theorem allNonNegative_nil : allNonNegative [] := trivial

theorem allNonNegative_cons {x : Int} {xs : List Int} :
    allNonNegative (x :: xs) ↔ x ≥ 0 ∧ allNonNegative xs := Iff.rfl

theorem allNonNegative_head {x : Int} {xs : List Int} (h : allNonNegative (x :: xs)) :
    x ≥ 0 := h.1

theorem allNonNegative_tail {x : Int} {xs : List Int} (h : allNonNegative (x :: xs)) :
    allNonNegative xs := h.2

-- =============================================================================
-- THEOREMS ABOUT processOrders
-- =============================================================================

-- Simp lemmas for reducing EffectM (which is Id) monadic operations
@[simp] theorem EffectM_bind_eq (m : EffectM α) (f : α → EffectM β) : m >>= f = f m := rfl
@[simp] theorem EffectM_pure_eq (x : α) : (pure x : EffectM α) = x := rfl
@[simp] theorem EffectM_map_eq (f : α → β) (m : EffectM α) : f <$> m = f m := rfl

-- Simp lemma to unfold List.foldlM for Id monad
@[simp] theorem List.foldlM_cons_Id (f : β → α → EffectM β) (b : β) (a : α) (as : List α) :
    List.foldlM f b (a :: as) = f b a >>= fun b' => List.foldlM f b' as := rfl

/-- Helper to get the multiplier as an Int (since EffectM = Id, this is just the identity). -/
noncomputable def multiplier : Int := getDiscountMultiplier ()

/-- Helper to get the threshold as an Int. -/
noncomputable def threshold : Int := getDiscountThreshold ()

/-- processOrders on an empty list yields zero revenue. -/
theorem processOrders_empty :
    processOrders [] ⊧ (· = 0) := rfl

/-- processOrders for a single order at or below threshold returns that order amount. -/
theorem processOrders_single_below_threshold
    (amount : Int)
    (h_below : ¬(amount > getDiscountThreshold ())) :
    processOrders [amount] ⊧ (· = amount) := by
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_below, ↓reduceIte]
  omega

/-- processOrders for a single order above threshold returns amount * multiplier. -/
theorem processOrders_single_above_threshold
    (amount : Int)
    (h_above : amount > threshold) :
    processOrders [amount] ⊧ (· = amount * multiplier) := by
  simp only [threshold] at h_above
  simp only [satisfies, processOrders, multiplier, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_above, ↓reduceIte]
  omega

/-- processOrders for two orders both below threshold returns their sum. -/
theorem processOrders_two_below_threshold
    (a b : Int)
    (ha : ¬(a > threshold))
    (hb : ¬(b > threshold)) :
    processOrders [a, b] ⊧ (· = a + b) := by
  simp only [threshold] at ha hb
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, ha, hb, ↓reduceIte]
  omega

/-- processOrders for two orders both above threshold: result is determined by multiplier. -/
theorem processOrders_two_above_threshold
    (a b : Int)
    (ha : a > threshold)
    (hb : b > threshold) :
    processOrders [a, b] ⊧ (· = a * multiplier + b * multiplier) := by
  simp only [threshold] at ha hb
  simp only [satisfies, processOrders, multiplier, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, ha, hb, ↓reduceIte]
  omega

/-- When multiplier is 1, orders above threshold contribute their original amount. -/
theorem processOrders_multiplier_one
    (amount : Int)
    (h_above : amount > getDiscountThreshold ())
    (h_mult : getDiscountMultiplier () = 1) :
    processOrders [amount] ⊧ (· = amount) := by
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_above, ↓reduceIte, h_mult]
  omega

/-- When multiplier is 0, orders above threshold contribute nothing. -/
theorem processOrders_multiplier_zero
    (amount : Int)
    (h_above : amount > getDiscountThreshold ())
    (h_mult : getDiscountMultiplier () = 0) :
    processOrders [amount] ⊧ (· = 0) := by
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_above, ↓reduceIte, h_mult]
  omega

/-- Revenue is non-negative for non-negative orders below threshold. -/
theorem processOrders_single_nonneg_below
    (amount : Int)
    (h_amount : amount ≥ 0)
    (h_below : ¬(amount > getDiscountThreshold ())) :
    processOrders [amount] ⊧ (· ≥ 0) := by
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_below, ↓reduceIte]
  omega

/-- Revenue is non-negative for non-negative orders above threshold with non-negative multiplier. -/
theorem processOrders_single_nonneg_above
    (amount : Int)
    (h_amount : amount ≥ 0)
    (h_above : amount > threshold)
    (h_mult : multiplier ≥ 0) :
    processOrders [amount] ⊧ (· ≥ 0) := by
  simp only [threshold] at h_above
  simp only [multiplier] at h_mult
  simp only [satisfies, processOrders, EffectM_bind_eq, EffectM_pure_eq,
             List.foldlM_cons_Id, List.foldlM_nil, h_above, ↓reduceIte]
  have h := Int.mul_nonneg h_amount h_mult
  omega
