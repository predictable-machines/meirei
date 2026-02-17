/-
  Except and Throw Examples

  Demonstrates throw statements in Meirei IR functions returning Except(E, T).
  Throw acts as early return wrapping in Except.error.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

-- Lean's Except doesn't have BEq by default; needed for #guard assertions
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

-- Case 1: Pure throw (no loop)
-- throw → Except.error, return → Except.ok
-- if-then guard nesting transforms: if (x < 0) { throw "negative"; } return x;
-- into: if x < 0 then Except.error "negative" else Except.ok x
def validate := [Meirei|
  def validate(x: Int): Except(String, Int) {
    if (x < 0) { throw "negative"; }
    return x;
  }
]

#meirei_print validate
#guard validate 5 == Except.ok 5
#guard validate (-1) == Except.error "negative"

-- Case 2: Throw in loop with accumulation
-- Uses Except fold: accumulator is Except(String, Int), short-circuits on error.
-- After fold, continuation uses >>= to propagate errors, pure for Except.ok.
def sumPositive := [Meirei|
  def sumPositive(nums: [Int]): Except(String, Int) {
    var total: Int = 0;
    for x in nums {
      if (x < 0) { throw "negative found"; }
      total = total + x;
    }
    return total;
  }
]

#meirei_print sumPositive
#guard sumPositive [1, 2, 3] == Except.ok 6
#guard sumPositive [1, -2, 3] == Except.error "negative found"

-- Case 3: Multiple validation guards
-- Each throw guard nests as another if-then-else level in the output.
def validateRange := [Meirei|
  def validateRange(x: Int): Except(String, Int) {
    if (x < 0) { throw "negative"; }
    if (x == 0) { throw "zero not allowed"; }
    if (x > 1000) { throw "too large"; }
    return x;
  }
]

#meirei_print validateRange
#guard validateRange (-5) == Except.error "negative"
#guard validateRange 0 == Except.error "zero not allowed"
#guard validateRange 1001 == Except.error "too large"
#guard validateRange 42 == Except.ok 42

-- Case 4: Computation between guards
-- Variable declarations create let-bindings; a later guard checks the computed result.
def safeDivMod := [Meirei|
  def safeDivMod(a: Int, b: Int): Except(String, Int) {
    if (b == 0) { throw "division by zero"; }
    var q: Int = a / b;
    var r: Int = a % b;
    if (q == 0) { throw "quotient is zero"; }
    return q + r;
  }
]

#meirei_print safeDivMod
#guard safeDivMod 10 0 == Except.error "division by zero"
#guard safeDivMod 3 10 == Except.error "quotient is zero"
#guard safeDivMod 10 3 == Except.ok 4

-- Case 5: Guards followed by if-else branching
-- After validation, each branch of the if-else returns a different computation.
def classifyAndScale := [Meirei|
  def classifyAndScale(score: Int, factor: Int): Except(String, Int) {
    if (score < 0) { throw "negative score"; }
    if (score > 100) { throw "score out of range"; }
    if (score >= 50) {
      return score * factor;
    } else {
      return score + factor;
    }
  }
]

#meirei_print classifyAndScale
#guard classifyAndScale (-5) 2 == Except.error "negative score"
#guard classifyAndScale 101 2 == Except.error "score out of range"
#guard classifyAndScale 60 3 == Except.ok 180
#guard classifyAndScale 30 5 == Except.ok 35

-- Case 6: Pre-loop validation combined with throw inside the loop
-- The guard before the loop nests as if-then-else.
-- The loop uses the Except fold strategy; post-loop continuation uses >>= for error propagation.
def sumBounded := [Meirei|
  def sumBounded(nums: [Int], bound: Int): Except(String, Int) {
    if (bound <= 0) { throw "bound must be positive"; }
    var total: Int = 0;
    for x in nums {
      if (x > bound) { throw "element exceeds bound"; }
      total = total + x;
    }
    return total;
  }
]

#meirei_print sumBounded
#guard sumBounded [1, 2, 3] 10 == Except.ok 6
#guard sumBounded [1, 2, 3] 0 == Except.error "bound must be positive"
#guard sumBounded [1, 20, 3] 10 == Except.error "element exceeds bound"

-- ========= Effectful + Throw Examples =========

-- Each effectful operation has its own error type. The caller's error type is a
-- sum that wraps each operation's errors alongside the caller's own throw cases.
-- The EffectM monad is inferred from the effectful bind operations.

inductive FetchAmountError where
  | orderNotFound
  deriving Repr, BEq

inductive FetchDiscountError where
  | noData
  deriving Repr, BEq

inductive ProcessOrderError where
  | fetchAmount : FetchAmountError → ProcessOrderError
  | fetchDiscount : FetchDiscountError → ProcessOrderError
  | invalidAmount : ProcessOrderError
  | discountExceedsAmount : ProcessOrderError
  deriving Repr, BEq

abbrev EffectM (ε : Type) (α : Type) := Except ε α

-- Each helper wraps its domain error into the caller's sum type
def fetchAmount (orderId : Int) : EffectM ProcessOrderError Int :=
  if orderId == 0 then .error (.fetchAmount .orderNotFound) else .ok (orderId - 3)

def fetchDiscount (orderId : Int) : EffectM ProcessOrderError Int :=
  if orderId > 100 then .error (.fetchDiscount .noData) else .ok (orderId / 2)

-- Case 7: Effectful binds interleaved with throw guards
-- Effectful binds (<-) set effectful mode, so throw generates monadic `throw`
-- and return generates `pure`. Errors from helper functions propagate via >>=.
-- The function's own throws use the sum type's local variants.
def processOrder := [Meirei|
  def processOrder(orderId: Int): Int {
    amount <- fetchAmount(orderId);
    if (amount <= 0) { throw ProcessOrderError.invalidAmount; }
    discount <- fetchDiscount(orderId);
    var total: Int = amount - discount;
    if (total < 0) { throw ProcessOrderError.discountExceedsAmount; }
    return total;
  }
]

#meirei_print processOrder
#guard processOrder 0 == Except.error (.fetchAmount .orderNotFound)
#guard processOrder 2 == Except.error .invalidAmount
#guard processOrder 4 == Except.error .discountExceedsAmount
#guard processOrder 200 == Except.error (.fetchDiscount .noData)
#guard processOrder 10 == Except.ok 2

-- ========= Edge Cases for Except Fold =========

-- Case 8: Nested throws in loop (throw in nested if)
-- Tests that nested conditionals with throw work correctly inside loops.
def sumPositiveEvenOnly := [Meirei|
  def sumPositiveEvenOnly(nums: [Int]): Except(String, Int) {
    var total: Int = 0;
    for x in nums {
      if (x < 0) {
        throw "negative found";
      }
      if (x % 2 != 0) {
        throw "odd number found";
      }
      total = total + x;
    }
    return total;
  }
]

#meirei_print sumPositiveEvenOnly
#guard sumPositiveEvenOnly [2, 4, 6] == Except.ok 12
#guard sumPositiveEvenOnly [2, (-1), 6] == Except.error "negative found"
#guard sumPositiveEvenOnly [2, 3, 6] == Except.error "odd number found"

-- Case 9: Multiple variables modified in Except fold loop
-- Tests that loop with throw can still accumulate into multiple variables.
def sumAndCount := [Meirei|
  def sumAndCount(nums: [Int], limit: Int): Except(String, Int) {
    var total: Int = 0;
    var count: Int = 0;
    for x in nums {
      if (x > limit) { throw "exceeds limit"; }
      total = total + x;
      count = count + 1;
    }
    return total + count;
  }
]

#meirei_print sumAndCount
#guard sumAndCount [1, 2, 3] 10 == Except.ok 9  -- sum=6, count=3
#guard sumAndCount [1, 20, 3] 10 == Except.error "exceeds limit"

-- Case 10: Throw with computation before it in loop
-- Tests that computation before a throw in a loop body works correctly.
def sumWithMax := [Meirei|
  def sumWithMax(nums: [Int], maxSum: Int): Except(String, Int) {
    var total: Int = 0;
    for x in nums {
      var newTotal: Int = total + x;
      if (newTotal > maxSum) { throw "sum exceeded max"; }
      total = newTotal;
    }
    return total;
  }
]

#meirei_print sumWithMax
#guard sumWithMax [1, 2, 3] 100 == Except.ok 6
#guard sumWithMax [1, 2, 3] 5 == Except.error "sum exceeded max"
#guard sumWithMax [10, 20] 15 == Except.error "sum exceeded max"

-- Case 11: Early return guard tests (showing optimization for if-then guards)
-- The early return guard optimization transforms: if (c) { return v; } rest
-- into: if c then v else rest. Works for both return and throw.
def validateMultiple := [Meirei|
  def validateMultiple(x: Int, y: Int): Except(String, Int) {
    if (x < 0) { return 0; }
    if (y < 0) { throw "y is negative"; }
    if (x == 0) { return y; }
    return x + y;
  }
]

#meirei_print validateMultiple
#guard validateMultiple (-5) 10 == Except.ok 0    -- early return guard
#guard validateMultiple 5 (-10) == Except.error "y is negative"
#guard validateMultiple 0 10 == Except.ok 10      -- early return on x == 0
#guard validateMultiple 5 10 == Except.ok 15
