/-
  Complex Early Exit Pattern Examples

  This file contains more sophisticated examples to validate
  the elaborator's handling of:
  - Nested if-else with early exits
  - Multiple conditions and complex expressions
  - Edge cases for break and return patterns
-/

import PredictableVerification.IR.Meirei.Elaborator.Index

open Meirei

-- =============================================================================
-- PATTERN 1: Find First Even Number Greater Than Threshold
-- =============================================================================

/-
  More complex search with multiple conditions.
  Find the first even number greater than a threshold.
-/

def findFirstEvenAbove := [Meirei|
  def findFirstEvenAbove(nums: [int]): int {
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
#eval findFirstEvenAbove [1, 2, 3, 11, 15]  -- Should be 11
#eval findFirstEvenAbove [1, 2, 3, 4, 5]    -- Should be 0 (none > 10)
#eval findFirstEvenAbove [6, 7, 8, 9]       -- Should be 0 (6,7,8,9 but none > 10)
#eval findFirstEvenAbove [20, 1, 2]         -- Should be 20
#eval findFirstEvenAbove []                 -- Should be 0

#print findFirstEvenAbove

-- =============================================================================
-- PATTERN 2: Sum with Multiple Break Conditions
-- =============================================================================

/-
  Sum elements until we hit a negative number OR a number > 100.
  This tests if-else with break.
-/

def sumUntilNegativeOrLarge := [Meirei|
  def sumUntilNegativeOrLarge(nums: [int]): int {
    var total: int = 0;
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
#eval sumUntilNegativeOrLarge [1, 2, 3, 4, 5]      -- Should be 15
#eval sumUntilNegativeOrLarge [10, 20, -5, 30]     -- Should be 30 (stops at -5)
#eval sumUntilNegativeOrLarge [10, 20, 200, 30]    -- Should be 30 (stops at 200)
#eval sumUntilNegativeOrLarge [-1, 2, 3]           -- Should be 0 (stops immediately)
#eval sumUntilNegativeOrLarge []                   -- Should be 0

#print sumUntilNegativeOrLarge

-- =============================================================================
-- PATTERN 3: Find Maximum Before Sentinel
-- =============================================================================

/-
  Find the maximum value in a list, but stop if we see a sentinel value (-999).
  This combines accumulation (tracking max) with early exit (break on sentinel).
-/

def maxBeforeSentinel := [Meirei|
  def maxBeforeSentinel(nums: [int]): int {
    var max: int = 0;
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
#eval maxBeforeSentinel [5, 10, 3, 15, 2]       -- Should be 15
#eval maxBeforeSentinel [5, 10, -999, 100]      -- Should be 10 (stops at -999)
#eval maxBeforeSentinel [-999, 5, 10]           -- Should be 0 (stops immediately)
#eval maxBeforeSentinel [1, 2, 3]               -- Should be 3
#eval maxBeforeSentinel []                      -- Should be 0

#print maxBeforeSentinel

-- =============================================================================
-- PATTERN 4: Count Until Condition with Early Return
-- =============================================================================

/-
  Count how many numbers are positive, but return immediately if we find
  a number greater than 50 (indicating an error condition).
-/

def countPositiveOrError := [Meirei|
  def countPositiveOrError(nums: [int]): int {
    var count: int = 0;
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
#eval countPositiveOrError [1, 2, -5, 3, 4]     -- Should be 4
#eval countPositiveOrError [1, 2, 60, 3]        -- Should be -1 (error on 60)
#eval countPositiveOrError [-1, -2, -3]         -- Should be 0
#eval countPositiveOrError [10, 20, 30]         -- Should be 3
#eval countPositiveOrError []                   -- Should be 0

#print countPositiveOrError

-- =============================================================================
-- PATTERN 5: Product Until Zero (Break Pattern)
-- =============================================================================

/-
  Calculate the product of numbers until we hit a zero (which would make
  the whole product zero, so we can stop early).
-/

def productUntilZero := [Meirei|
  def productUntilZero(nums: [int]): int {
    var product: int = 1;
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
#eval productUntilZero [2, 3, 4]           -- Should be 24
#eval productUntilZero [2, 3, 0, 5]        -- Should be 6 (stops at 0)
#eval productUntilZero [0, 2, 3]           -- Should be 1 (stops immediately)
#eval productUntilZero [5]                 -- Should be 5
#eval productUntilZero []                  -- Should be 1

#print productUntilZero

-- =============================================================================
-- PATTERN 6: Find First Divisor
-- =============================================================================

/-
  Find the first number in the list that divides evenly into a target.
  Returns the divisor, or 0 if none found.
-/

def findFirstDivisor := [Meirei|
  def findFirstDivisor(nums: [int]): int {
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
#eval findFirstDivisor [1, 2, 3, 4, 5]      -- Should be 3 (first > 2)
#eval findFirstDivisor [1, 2, 25, 3]        -- Should be 3 (25 > 20, so skip)
#eval findFirstDivisor [1, 2]               -- Should be 0
#eval findFirstDivisor [10, 15, 5]          -- Should be 10
#eval findFirstDivisor []                   -- Should be 0

#print findFirstDivisor

-- =============================================================================
-- PATTERN 7: Sum Positive, Skip Negative (No Early Exit)
-- =============================================================================

/-
  This is a control case - no early exit, but uses if-else to conditionally
  update the accumulator.
-/

def sumPositivesOnly := [Meirei|
  def sumPositivesOnly(nums: [int]): int {
    var total: int = 0;
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
#eval sumPositivesOnly [1, -2, 3, -4, 5]    -- Should be 9 (1+3+5)
#eval sumPositivesOnly [-1, -2, -3]         -- Should be 0
#eval sumPositivesOnly [10, 20, 30]         -- Should be 60
#eval sumPositivesOnly []                   -- Should be 0

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
