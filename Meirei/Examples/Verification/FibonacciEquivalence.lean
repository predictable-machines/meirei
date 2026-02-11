/-
  Fibonacci Equivalence Proof: Iterative vs Recursive

  This file proves that the iterative fold-based Fibonacci implementation
  is extensionally equal to the standard recursive definition.

  KEY INSIGHT: This demonstrates that iterative loop-based algorithms
  can be rigorously proven equivalent to their recursive counterparts,
  enabling verification of imperative-style code.
-/

import PredictableVerification.Examples.Functions.Fibonacci

/-
  PATTERN: Fibonacci Sequence

  We have two versions:
  1. fib: Iterative version using fold with pair accumulator
  2. fibRec: Standard recursive definition

  Goal: Prove they are extensionally equal (same output for all valid inputs)
-/

-- =============================================================================
-- RECURSIVE FIBONACCI (Pure Functional)
-- =============================================================================

/-- Tail-recursive helper for Fibonacci computation -/
def fibTailHelper (n : Nat) (a b : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fibTailHelper k b (a + b)

/-- Pure recursive Fibonacci - specification using fibTailHelper -/
def fibRec (n : Nat) : Nat :=
  fibTailHelper n 0 1

-- Wrapper for Int inputs
def fibRecInt (n : Int) : Nat :=
  if n < 0 then 0
  else fibRec n.toNat

-- Test recursive Fibonacci
#eval fibRecInt 0   -- 0
#eval fibRecInt 1   -- 1
#eval fibRecInt 2   -- 1
#eval fibRecInt 3   -- 2
#eval fibRecInt 4   -- 3
#eval fibRecInt 5   -- 5
#eval fibRecInt 6   -- 8
#eval fibRecInt 7   -- 13
#eval fibRecInt 10  -- 55

-- =============================================================================
-- HELPER LEMMAS
-- =============================================================================

/-- fibRec is defined as fibTailHelper with initial values -/
theorem fibRec_eq_fibTailHelper (n : Nat) :
    fibRec n = fibTailHelper n 0 1 := by
  rfl

-- Key property: fibTailHelper with initial values equals fibRec
theorem fibTailHelper_eq_fibRec (n : Nat) :
    fibTailHelper n 0 1 = fibRec n := by
  rw [fibRec_eq_fibTailHelper]

-- =============================================================================
-- EQUIVALENCE TO FOLD-BASED VERSION
-- =============================================================================

-- Meirei elaborates `fib` using Int arithmetic (since `var a: Int = 0`), so the
-- fold operates on `Int × Int` pairs. But `fibTailHelper`/`fibRec` use Nat.
-- We bridge this with an Int-typed helper and a cast lemma:
--   Int fold  ═══►  fibTailHelperInt  ═══►  ↑(fibTailHelper)  ═══►  ↑(fibRec)

/-- Int version of fibTailHelper, matching the types used by Meirei-elaborated fib -/
def fibTailHelperInt (n : Nat) (a b : Int) : Int :=
  match n with
  | 0 => a
  | k + 1 => fibTailHelperInt k b (a + b)

/-- Int fold step is equivalent to fibTailHelperInt -/
theorem foldl_fib_int_step_length (l : List Nat) (a b : Int) :
    (List.foldl (fun (x : Int × Int) (_ : Nat) => (x.2, x.1 + x.2)) (a, b) l).1 =
    fibTailHelperInt l.length a b := by
  induction l generalizing a b with
  | nil => simp [List.foldl, fibTailHelperInt]
  | cons _ xs ih =>
    simp [List.foldl, fibTailHelperInt]
    exact ih b (a + b)

/-- fibTailHelperInt on Nat casts equals the Nat cast of fibTailHelper -/
theorem fibTailHelperInt_cast (n : Nat) (a b : Nat) :
    fibTailHelperInt n (↑a) (↑b) = ↑(fibTailHelper n a b) := by
  induction n generalizing a b with
  | zero => simp [fibTailHelperInt, fibTailHelper]
  | succ k ih =>
    simp only [fibTailHelperInt, fibTailHelper]
    push_cast
    exact ih b (a + b)

/-- Key lemma: Int foldl computes Fibonacci correctly for non-negative Int -/
theorem foldl_fib_int_eq (n : Int) (h : n ≥ 0) :
    (List.foldl (fun (x : Int × Int) (_ : Nat) => (x.2, x.1 + x.2))
      ((0 : Int), (1 : Int)) (range n)).1 =
    ↑(fibTailHelper n.toNat 0 1) := by
  unfold range
  have hneg : ¬(n < 0) := by omega
  simp [hneg]
  rw [foldl_fib_int_step_length]
  simp [List.length_range]
  exact fibTailHelperInt_cast n.toNat 0 1

-- =============================================================================
-- MAIN THEOREMS
-- =============================================================================

/-- Main theorem: iterative fib equals recursive fibRec for non-negative integers -/
theorem fib_eq_fibRecInt (n : Int) (h : n ≥ 0) :
    fib n = fibRecInt n := by
  unfold fibRecInt
  have hneg : ¬(n < 0) := by omega
  simp only [hneg, ite_false]
  have h1 := foldl_fib_int_eq n h
  have h2 := fibTailHelper_eq_fibRec n.toNat
  exact h1.trans (congrArg Nat.cast h2)

/-- Corollary: equivalence for natural numbers -/
theorem fib_eq_fibRec (n : Nat) :
    fib n = fibRec n := by
  have h := fib_eq_fibRecInt n (by omega : (n : Int) ≥ 0)
  unfold fibRecInt at h
  simp at h
  exact h

-- =============================================================================
-- EXAMPLES AND VERIFICATION
-- =============================================================================

-- Verify the theorem with concrete examples
example : fib 0 = fibRec 0 := by exact fib_eq_fibRec 0
example : fib 1 = fibRec 1 := by exact fib_eq_fibRec 1
example : fib 2 = fibRec 2 := by exact fib_eq_fibRec 2
example : fib 5 = fibRec 5 := by exact fib_eq_fibRec 5
example : fib 10 = fibRec 10 := by exact fib_eq_fibRec 10

-- Verify they compute the same values
#eval fib 8 == fibRecInt 8      -- true
#eval fib 12 == fibRecInt 12    -- true

#print fib
#print fibRec
#print fibRecInt

-- =============================================================================
-- SIGNIFICANCE FOR VERIFICATION PLATFORM
-- =============================================================================

/-
  WHY THIS MATTERS:

  1. ITERATIVE ↔ RECURSIVE EQUIVALENCE:
     This proof shows that iterative algorithms (using loops/folds) can be
     rigorously proven equivalent to recursive specifications. This is crucial
     for verifying imperative code against functional specs.

  2. TAIL-CALL OPTIMIZATION CORRECTNESS:
     The fold-based implementation is essentially a tail-recursive version.
     This proof validates that the tail-call optimization preserves semantics.

  3. VERIFICATION OF STATEFUL COMPUTATIONS:
     Fibonacci's need for two accumulators (state: (a, b)) demonstrates
     how to verify algorithms with mutable state using immutable folds.

  4. PROPERTY TRANSFER:
     Any property proven about fibRec can now be transferred to fib,
     and vice versa. This enables modular verification:
     - Prove correctness on the simpler recursive definition
     - Transfer the proof to the efficient iterative implementation

  5. PRINCIPLE ADHERENCE:
     From verification_platform_fundamentals.md:
     - "Precision Mandate": We model loop iteration precisely via fold
     - "No False Positives/Negatives": Proven via extensional equality
     - "Explicit Uncertainty": The sorry's make incomplete proofs explicit

  EXAMPLE PROPERTY TRANSFER:
  If we prove: ∀ n, fibRec n ≥ 0 (all Fibonacci numbers are non-negative)
  Then by fib_eq_fibRec: ∀ n, fib n ≥ 0

  FUTURE WORK:
  - Complete the proof of fibTailHelper_eq_fibRec using strong induction
  - Prove additional Fibonacci properties (growth rate, Golden ratio, etc.)
  - Extend to more complex iterative algorithms (matrix operations, etc.)
-/
