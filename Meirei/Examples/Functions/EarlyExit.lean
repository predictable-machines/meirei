/-
  Early Exit Pattern Examples

  This file demonstrates how imperative loops with early exits
  (break, early return) are transformed into functional folds
  using Option accumulators.

  KEY PATTERN: When a loop can exit early, the accumulator wraps
  the result in Option:
  - Some x: Continue processing with value x
  - None: Stop processing (exit condition met)
-/

import PredictableVerification.IR.Meirei.Elaborator

open Meirei

-- =============================================================================
-- PATTERN 1: Find First Element (Early Return)
-- =============================================================================

/-
  Problem: Find the first element in a list that is greater than 10.
  Return 0 if not found.

  Imperative version:
    for elem in list {
      if (elem > 10) { return elem; }  -- early exit!
    }
    return 0;

  Functional transformation:
    - Accumulator type: Option Int
    - None = still searching
    - Some x = found the element (stop searching)
    - At the end, extract with getD to get 0 if None
-/

def findFirstGreaterThan10 := [Meirei|
  def findFirstGreaterThan10(nums: [int]): int {
    for x in nums {
      if (x > 10) {
        return x;
      }
    }
    return 0;
  }
]

#check findFirstGreaterThan10  -- findFirstGreaterThan10 : List Int → Int

-- Test cases
#eval findFirstGreaterThan10 [1, 5, 3, 15, 20]  -- Should be 15 (first > 10)
#eval findFirstGreaterThan10 [1, 2, 3]          -- Should be 0 (none > 10)
#eval findFirstGreaterThan10 [20, 30, 5]        -- Should be 20 (first element)
#eval findFirstGreaterThan10 []                 -- Should be 0 (empty list)

-- Show the generated code
#print findFirstGreaterThan10
/-
  The generated code uses Option accumulator:

  def findFirstGreaterThan10 (nums : List Int) : Int :=
    let result := List.foldl (fun acc x =>
      match acc with
      | some found => some found  -- already found, keep it
      | none =>
          if x > 10 then some x   -- found it!
          else none               -- keep searching
    ) none nums
    result.getD 0                 -- extract, default to 0
-/

-- =============================================================================
-- PATTERN 2: Accumulate Until Condition (Break)
-- =============================================================================

/-
  Problem: Sum elements of a list until we see an element > 100,
  then stop (don't include elements after the first > 100).

  Imperative version:
    acc = 0
    for elem in list {
      if (elem > 100) { break; }  -- stop here!
      acc = acc + elem;
    }
    return acc;

  Functional transformation:
    - Accumulator type: (Bool, Int)
    - (true, acc) = continue processing with accumulator value acc
    - (false, acc) = stopped (break encountered), preserve acc
    - At the end, extract .2 to get the accumulated value
-/

def sumUntilLarge := [Meirei|
  def sumUntilLarge(nums: [int]): int {
    var total: int = 0;
    for x in nums {
      if (x > 100) {
        break;
      }
      total = total + x;
    }
    return total;
  }
]

#check sumUntilLarge  -- sumUntilLarge : List Int → Int

-- Test cases
#eval sumUntilLarge [1, 2, 3, 4, 5]       -- Should be 15 (sum all)
#eval sumUntilLarge [10, 20, 200, 30]     -- Should be 30 (stop at 200)
#eval sumUntilLarge [150, 1, 2]           -- Should be 0 (stop immediately)
#eval sumUntilLarge []                    -- Should be 0 (empty)

-- Show the generated code
#print sumUntilLarge
/-
  The generated code uses (Bool, Int) accumulator:

  def sumUntilLarge (nums : List Int) : Int :=
    let finalState := List.foldl (fun state x =>
      match state with
      | (false, value) => (false, value)   -- already stopped, keep value
      | (true, total) =>
          if x > 100 then (false, total)   -- condition met, break with current value
          else (true, total + x)           -- continue accumulating
    ) (true, 0) nums
    finalState.2                           -- extract accumulated value
-/

-- =============================================================================
-- PATTERN 3: Find First Small Number
-- =============================================================================

/-
  Another find-first example: find the first number less than 5.
  This demonstrates the pattern is general for any search condition.
-/

def findFirstSmall := [Meirei|
  def findFirstSmall(nums: [int]): int {
    for n in nums {
      if (n < 5) {
        return n;
      }
    }
    return 100;
  }
]

#check findFirstSmall
#print findFirstSmall -- findFirstSmall : List Int → Int

-- Test cases
#eval findFirstSmall [10, 20, 3, 8, 1]  -- Should be 3 (first < 5)
#eval findFirstSmall [10, 20, 30]       -- Should be 100 (not found)
#eval findFirstSmall [2, 1]             -- Should be 2 (first element)
#eval findFirstSmall []                 -- Should be 100 (empty)


-- =============================================================================
-- KEY INSIGHTS
-- =============================================================================

/-
  1. TWO ENCODING PATTERNS:

     a) FIND-FIRST (Option Int):
        - None = still searching
        - Some x = found element x (stop searching)
        - Extract with Option.getD to provide default for "not found"

     b) BREAK-WITH-VALUE ((Bool, Int)):
        - (true, x) = continue processing with value x
        - (false, x) = stopped (break encountered), preserve value x
        - Extract with .2 to get the accumulated value

  2. ONCE STOPPED, STAY STOPPED:
     The match expression ensures that once we transition to the
     terminal state, we stay there and ignore remaining elements.

  3. WHY DIFFERENT ENCODINGS:
     - Find-first: We don't have a meaningful value until found → Option
     - Break: We always have an accumulated value to preserve → (Bool, Int)

  4. SEMANTIC EQUIVALENCE:
     These transformations preserve the exact semantics of the imperative
     version, which is critical for verification (no false positives/negatives).

  5. EXPLICITNESS:
     The encoding makes the "early exit" control flow explicit in the
     data structure, rather than implicit in control flow (adheres to
     "Explicit over Implicit" principle from verification_platform_fundamentals.md).
-/

-- =============================================================================
-- COMPARISON: With vs Without Early Exit
-- =============================================================================

/-
  Compare behavior with and without early exit:

  WITH early exit (sumUntilLarge):
    [1, 2, 3, 200, 4, 5] → 6 (stops at 200: 1+2+3 = 6)

  WITHOUT early exit (would sum all elements):
    [1, 2, 3, 200, 4, 5] → 215 (includes all: 1+2+3+200+4+5 = 215)

  The (Bool, Int) tuple wrapper makes the early-exit control flow
  explicit in the data structure (adheres to "Explicit over Implicit"
  from verification_platform_fundamentals.md).
-/

-- Test the with-early-exit version
#eval sumUntilLarge [1, 2, 3, 200, 4, 5]  -- 6 (stops at 200)
