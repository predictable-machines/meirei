/-
  EffectM with error type as a parameter

  EffectM ε α represents a computation that may:
    1. Succeed with a value of type α
    2. Fail with an error of type ε
    3. Have side effects (modeled abstractly)

  This makes the error type part of the monad itself, similar to ExceptT.
-/

import PredictableVerification.IR.Meirei.Elaborator.Index

namespace EffectMParameterized

-- ============================================================================
-- Core EffectM Definition
-- ============================================================================

abbrev EffectM (ε : Type) (α : Type) := Except ε α

-- For effectful operations that can't fail, we use Empty as the error type
abbrev EffectMNoError (α : Type) := EffectM Empty α

-- ============================================================================
-- Error Types
-- ============================================================================

inductive ArrayGetError where
  | indexOutOfBounds : Int → Nat → ArrayGetError  -- index, array size
  deriving Repr, DecidableEq

-- ============================================================================
-- Effectful Operations (Axiomatized)
-- ============================================================================

axiom arrayGet : List α → Int → EffectM ArrayGetError α

-- ============================================================================
-- Satisfies Predicates
-- ============================================================================

-- Succeeds predicate: the computation returns Ok
def succeeds (m : EffectM ε α) : Prop :=
  match m with
  | .ok _ => True
  | .error _ => False

-- Total correctness: computation succeeds AND result satisfies P
def satisfies (m : EffectM ε α) (P : α → Prop) : Prop :=
  match m with
  | .ok a => P a
  | .error _ => False

notation:50 m " ⊧ " P => satisfies m P

-- Partial correctness: IF the computation succeeds, THEN result satisfies P
-- Trivially holds for errors
def satisfiesPartial (m : EffectM ε α) (P : α → Prop) : Prop :=
  match m with
  | .ok a => P a
  | .error _ => True

notation:50 m " ⊧! " P => satisfiesPartial m P

end EffectMParameterized
