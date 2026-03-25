/-
  Effectful Equivalence Proof: Hand-written vs Meirei-elaborated

  This file proves theorems about effectful functions, demonstrating that
  the Meirei-elaborated version is definitionally equal to the hand-written
  version and satisfies the same properties.
-/

import Meirei.Examples.Functions.Effectful

open Effectful

-- =============================================================================
-- EFFECT SPECIFICATIONS
-- =============================================================================

/-- Predicate for even integers -/
def isEven (n : Int) : Prop := ∃ k, n = 2 * k

/-- Assumption about getY: it always returns an even number -/
axiom getY_even : getY () ⊧ isEven

-- =============================================================================
-- THEOREMS FOR HAND-WRITTEN VERSION
-- =============================================================================

theorem prodOfTwoWithEffect_zero : prodOfTwoWithEffect 0 = pure 0 := by
  simp only [prodOfTwoWithEffect, Int.zero_mul]
  rfl

theorem prodOfTwoWithEffect_even (x : Int) : prodOfTwoWithEffect x ⊧ isEven := by
  unfold satisfies
  obtain ⟨k, hk⟩ := getY_even
  refine ⟨k * x, ?_⟩
  simp only [prodOfTwoWithEffect, hk, bind, pure]
  rw [Int.mul_comm x, Int.mul_assoc]

-- =============================================================================
-- EQUIVALENCE OF MEIREI AND HAND-WRITTEN VERSIONS
-- =============================================================================

-- Verify that both versions are definitionally equivalent
example : prodOfTwoWithEffect' = prodOfTwoWithEffect := rfl

-- =============================================================================
-- THEOREMS FOR MEIREI VERSION
-- =============================================================================

-- The Meirei version also satisfies the same theorems
theorem prodOfTwoWithEffect'_zero : prodOfTwoWithEffect' 0 = pure 0 := by
  simp only [prodOfTwoWithEffect', Int.zero_mul]
  rfl

theorem prodOfTwoWithEffect'_even (x : Int) : prodOfTwoWithEffect' x ⊧ isEven := by
  -- Can reuse the proof since the functions are definitionally equal
  exact prodOfTwoWithEffect_even x
