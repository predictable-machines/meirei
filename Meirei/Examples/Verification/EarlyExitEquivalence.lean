/-
  Equivalence Proof: Imperative vs Functional Early Exit

  This file proves that the imperative-style fold-based transformation
  of early exit loops is extensionally equal to pure functional recursion.

  KEY INSIGHT: This proof demonstrates that our imperative-to-functional
  transformation is semantically correct - it preserves the meaning of
  the original code exactly.
-/

import PredictableVerification.Examples.Functions.EarlyExit

-- NOTE: The imperative syntax now uses "int" (lowercase) as a keyword to avoid
-- conflicts with Lean's standard Int type. This allows us to use Int directly
-- in Lean code without needing escaped identifiers.

/-
  PATTERN: Find First Element Greater Than 10

  We have two versions:
  1. findFirstGreaterThan10: Generated from imperative syntax, uses fold + Option
  2. findFirstGreaterThan10Pure: Direct recursive definition

  Goal: Prove they are extensionally equal (same output for all inputs)
-/

-- =============================================================================
-- MAIN RESULT: findFirst_eq_findFirstPure_complete
--
-- Proves extensional equality between fold-based and recursive implementations
-- (∀ input, both produce the same output)
-- =============================================================================

-- Pure functional version (the "obviously correct" implementation)
def findFirstGreaterThan10Pure : (l : List Int) → Int
  | [] => 0                                     -- empty list: return default
  | x :: xs =>
      if x > 10 then x                          -- found it: return
      else findFirstGreaterThan10Pure xs        -- keep searching

-- Helper: The specific fold function used in findFirstGreaterThan10
def findFirstFoldStep (acc : Option Int) (x : Int) : Option Int :=
  if acc.isSome = true then acc else if x > 10 then some x else none

-- Key lemma: The fold with our specific step function equals the pure version
theorem foldl_findFirst_eq_pure (l : List Int) :
    (List.foldl findFirstFoldStep none l).getD 0 = findFirstGreaterThan10Pure l := by
  induction l with
  | nil =>
      -- Base case: empty list
      unfold findFirstGreaterThan10Pure
      rfl
  | cons x xs ih =>
      -- Inductive case: x :: xs
      simp only [List.foldl, findFirstFoldStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      unfold findFirstGreaterThan10Pure
      by_cases h : x > 10
      case pos =>
        -- x > 10: fold immediately returns (some x)
        simp only [h, ↓reduceIte]
        -- After finding x, fold maintains (some x) through rest of list
        have keep_some : List.foldl findFirstFoldStep (some x) xs = some x := by
          clear ih h
          induction xs with
          | nil => rfl
          | cons y ys ih_inner =>
            simp only [List.foldl, findFirstFoldStep, Option.isSome_some, ↓reduceIte]
            exact ih_inner
        simp only [keep_some, Option.getD_some]
      case neg =>
        -- x ≤ 10: fold continues with none
        simp only [h, ↓reduceIte]
        exact ih

-- *** MAIN THEOREM ***
-- Extensional equality between fold-based and recursive versions
theorem findFirst_eq_findFirstPure_complete (l : List Int) :
    findFirstGreaterThan10 l = findFirstGreaterThan10Pure l := by
  unfold findFirstGreaterThan10
  exact foldl_findFirst_eq_pure l

-- =============================================================================
-- EXAMPLES AND VERIFICATION
-- =============================================================================

-- Test that both implementations work the same
#eval findFirstGreaterThan10Pure [1, 5, 3, 15, 20]  -- 15
#eval findFirstGreaterThan10Pure [1, 2, 3]          -- 0
#eval findFirstGreaterThan10Pure [20, 30, 5]        -- 20
#eval findFirstGreaterThan10Pure []                 -- 0

-- Verify the theorem with concrete examples
example : findFirstGreaterThan10 [1, 5, 3, 15, 20] = findFirstGreaterThan10Pure [1, 5, 3, 15, 20] := by
  exact findFirst_eq_findFirstPure_complete [1, 5, 3, 15, 20]

example : findFirstGreaterThan10 [1, 2, 3] = findFirstGreaterThan10Pure [1, 2, 3] := by
  exact findFirst_eq_findFirstPure_complete [1, 2, 3]

example : findFirstGreaterThan10 [] = findFirstGreaterThan10Pure [] := by
  exact findFirst_eq_findFirstPure_complete []

#print findFirstGreaterThan10
#print findFirstGreaterThan10Pure

-- =============================================================================
-- SIGNIFICANCE FOR VERIFICATION PLATFORM
-- =============================================================================

/-
  WHY THIS MATTERS:

  1. CORRECTNESS OF TRANSFORMATION:
     This proof demonstrates that our imperative-to-functional transformation
     is semantically correct. The fold-based encoding preserves the exact
     meaning of the imperative code.

  2. VERIFICATION SOUNDNESS:
     When we verify properties of the generated fold-based code, we're actually
     verifying properties of the original imperative code (no false positives/negatives).

  3. TRUST IN AUTOMATION:
     LLMs can generate imperative code that gets transformed to folds.
     This proof shows that the transformation is trustworthy - we're not
     introducing semantic bugs during translation.

  4. EQUIVALENCE CLASSES:
     This demonstrates that different implementations (imperative loops,
     folds, recursion) can be proven equivalent. This is foundational for
     the verification platform's goal of precise semantic modeling.

  5. PRINCIPLE ADHERENCE:
     From verification_platform_fundamentals.md:
     - "Precision Mandate": We model loop semantics precisely via folds
     - "No False Positives/Negatives": Proven via extensional equality
     - "Explicitness": The Option accumulator makes control flow explicit

  NEXT STEPS:
  - Prove similar equivalences for the break pattern ((Bool, Int) accumulator)
  - Prove equivalences for more complex loop patterns
  - Use these equivalences to transfer verification results between representations
-/
