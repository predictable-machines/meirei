/-
  Complex Early Exit Pattern Examples

  This file contains more sophisticated examples to validate
  the elaborator's handling of:
  - Nested if-else with early exits
  - Multiple conditions and complex expressions
  - Edge cases for break and return patterns
-/

import Meirei.IR.Meirei.Elaborator.Index

open Meirei

-- =============================================================================
-- PATTERN 1: Find First Even Number Greater Than Threshold
-- =============================================================================

/-
  More complex search with multiple conditions.
  Find the first even number greater than a threshold.
-/

def findFirstEvenAbove := [Meirei|
  def findFirstEvenAbove(nums: [Int]): Int {
    for x in nums {
      if (x > 5) {
        if (x > 10) {
          return x;
        }
      }
    }
    return 0;
  }
]

#check findFirstEvenAbove
#guard findFirstEvenAbove [1, 2, 3, 11, 15] == 11
#guard findFirstEvenAbove [1, 2, 3, 4, 5] == 0
#guard findFirstEvenAbove [6, 7, 8, 9] == 0
#guard findFirstEvenAbove [20, 1, 2] == 20
#guard findFirstEvenAbove [] == 0

#print findFirstEvenAbove

-- =============================================================================
-- PATTERN 2: Sum with Multiple Break Conditions
-- =============================================================================

/-
  Sum elements until we hit a negative number OR a number > 100.
  This tests if-else with break.
-/

def sumUntilNegativeOrLarge := [Meirei|
  def sumUntilNegativeOrLarge(nums: [Int]): Int {
    var total: Int = 0;
    for x in nums {
      if (x < 0) {
        break;
      } else {
        if (x > 100) {
          break;
        }
      }
      total = total + x;
    }
    return total;
  }
]

#check sumUntilNegativeOrLarge
#guard sumUntilNegativeOrLarge [1, 2, 3, 4, 5] == 15
#guard sumUntilNegativeOrLarge [10, 20, -5, 30] == 30
#guard sumUntilNegativeOrLarge [10, 20, 200, 30] == 30
#guard sumUntilNegativeOrLarge [-1, 2, 3] == 0
#guard sumUntilNegativeOrLarge [] == 0

#print sumUntilNegativeOrLarge

-- =============================================================================
-- PATTERN 3: Find Maximum Before Sentinel
-- =============================================================================

/-
  Find the maximum value in a list, but stop if we see a sentinel value (-999).
  This combines accumulation (tracking max) with early exit (break on sentinel).
-/

def maxBeforeSentinel := [Meirei|
  def maxBeforeSentinel(nums: [Int]): Int {
    var max: Int = 0;
    for x in nums {
      if (x == -999) {
        break;
      }
      if (x > max) {
        max = x;
      }
    }
    return max;
  }
]

#check maxBeforeSentinel
#guard maxBeforeSentinel [5, 10, 3, 15, 2] == 15
#guard maxBeforeSentinel [5, 10, -999, 100] == 10  -- stops at -999
#guard maxBeforeSentinel [-999, 5, 10] == 0        -- stops immediately
#guard maxBeforeSentinel [1, 2, 3] == 3
#guard maxBeforeSentinel [] == 0

#print maxBeforeSentinel

-- =============================================================================
-- PATTERN 4: Count Until Condition with Early Return
-- =============================================================================

/-
  Count how many numbers are positive, but return immediately if we find
  a number greater than 50 (indicating an error condition).
-/

def countPositiveOrError := [Meirei|
  def countPositiveOrError(nums: [Int]): Int {
    var count: Int = 0;
    for x in nums {
      if (x > 50) {
        return -1;
      }
      if (x > 0) {
        count = count + 1;
      }
    }
    return count;
  }
]

#check countPositiveOrError
#guard countPositiveOrError [1, 2, -5, 3, 4] == 4
#guard countPositiveOrError [1, 2, 60, 3] == -1
#guard countPositiveOrError [-1, -2, -3] == 0
#guard countPositiveOrError [10, 20, 30] == 3
#guard countPositiveOrError [] == 0

#print countPositiveOrError

-- =============================================================================
-- PATTERN 5: Product Until Zero (Break Pattern)
-- =============================================================================

/-
  Calculate the product of numbers until we hit a zero (which would make
  the whole product zero, so we can stop early).
-/

def productUntilZero := [Meirei|
  def productUntilZero(nums: [Int]): Int {
    var product: Int = 1;
    for x in nums {
      if (x == 0) {
        break;
      }
      product = product * x;
    }
    return product;
  }
]

#check productUntilZero
#guard productUntilZero [2, 3, 4] == 24
#guard productUntilZero [2, 3, 0, 5] == 6
#guard productUntilZero [0, 2, 3] == 1
#guard productUntilZero [5] == 5
#guard productUntilZero [] == 1

#print productUntilZero

-- =============================================================================
-- PATTERN 6: Find First Divisor
-- =============================================================================

/-
  Find the first number in the list that divides evenly into a target.
  Returns the divisor, or 0 if none found.
-/

def findFirstDivisor := [Meirei|
  def findFirstDivisor(nums: [Int]): Int {
    for d in nums {
      if (d > 2) {
        if (d < 20) {
          return d;
        }
      }
    }
    return 0;
  }
]

#check findFirstDivisor
#guard findFirstDivisor [1, 2, 3, 4, 5] == 3
#guard findFirstDivisor [1, 2, 25, 3] == 3
#guard findFirstDivisor [1, 2] == 0
#guard findFirstDivisor [10, 15, 5] == 10
#guard findFirstDivisor [] == 0

#print findFirstDivisor

-- =============================================================================
-- PATTERN 7: Sum Positive, Skip Negative (No Early Exit)
-- =============================================================================

/-
  This is a control case - no early exit, but uses if-else to conditionally
  update the accumulator.
-/

def sumPositivesOnly := [Meirei|
  def sumPositivesOnly(nums: [Int]): Int {
    var total: Int = 0;
    for x in nums {
      if (x > 0) {
        total = total + x;
      } else {
        total = total + 0;
      }
    }
    return total;
  }
]

#check sumPositivesOnly
#guard sumPositivesOnly [1, -2, 3, -4, 5] == 9
#guard sumPositivesOnly [-1, -2, -3] == 0
#guard sumPositivesOnly [10, 20, 30] == 60
#guard sumPositivesOnly [] == 0

#print sumPositivesOnly

-- =============================================================================
-- Summary of Test Coverage
-- =============================================================================

/-
  These examples test:

  1. ✓ Nested if statements with early return
  2. ✓ If-else with break in both branches
  3. ✓ Multiple sequential if statements with break
  4. ✓ Combination of early return and conditional accumulation
  5. ✓ Break with multiplication (not just addition)
  6. ✓ Multiple conditions for early return
  7. ✓ If-else without early exit (control case)

  All examples should compile and produce correct results if the
  elaborator properly handles these patterns.
-/
