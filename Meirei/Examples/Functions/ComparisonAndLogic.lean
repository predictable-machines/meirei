/-
  Comparison and Logic Operator Examples

  Demonstrates the comparison operators (<=, >=, !=, %)
  and logical operators (&&, ||, !) in Meirei.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace ComparisonAndLogic

-- =============================================================================
-- Comparison operators: <=, >=, !=
-- =============================================================================

-- Clamp a value to a range using <= and >=
def clamp := [Meirei|
  def clamp(x: Int, lo: Int, hi: Int): Int {
    if (x <= lo) {
      return lo;
    }
    if (x >= hi) {
      return hi;
    }
    return x;
  }
]

#check clamp
#guard clamp 5 0 10 == 5
#guard clamp (-3) 0 10 == 0
#guard clamp 15 0 10 == 10
#guard clamp 0 0 10 == 0   -- boundary: x == lo
#guard clamp 10 0 10 == 10 -- boundary: x == hi

-- Not-equal: return 0 if a == b, otherwise a - b
def diffOrZero := [Meirei|
  def diffOrZero(a: Int, b: Int): Int {
    if (a != b) {
      return a - b;
    }
    return 0;
  }
]

#check diffOrZero
#guard diffOrZero 10 3 == 7
#guard diffOrZero 5 5 == 0

-- =============================================================================
-- Modulo operator: %
-- =============================================================================

-- Check if a number is even (returns 1 for even, 0 for odd)
def isEven := [Meirei|
  def isEven(n: Int): Int {
    if (n % 2 == 0) {
      return 1;
    }
    return 0;
  }
]

#check isEven
#guard isEven 4 == 1
#guard isEven 7 == 0
#guard isEven 0 == 1

-- FizzBuzz-style classifier using modulo
-- Returns 3 for divisible by both, 2 for divisible by 5, 1 for divisible by 3, 0 otherwise
def fizzBuzzClassify := [Meirei|
  def fizzBuzzClassify(n: Int): Int {
    if (n % 3 == 0) {
      if (n % 5 == 0) {
        return 3;
      }
      return 1;
    }
    if (n % 5 == 0) {
      return 2;
    }
    return 0;
  }
]

#guard fizzBuzzClassify 15 == 3  -- both
#guard fizzBuzzClassify 9 == 1   -- div by 3
#guard fizzBuzzClassify 10 == 2  -- div by 5
#guard fizzBuzzClassify 7 == 0   -- neither

-- =============================================================================
-- Logical operators: &&, ||, !
-- =============================================================================

-- Logical AND: check if a value is within a range (exclusive)
def inRange := [Meirei|
  def inRange(x: Int, lo: Int, hi: Int): Bool {
    return (x > lo) && (x < hi);
  }
]

#check inRange
#guard inRange 5 0 10 == true
#guard inRange 0 0 10 == false   -- boundary
#guard inRange 10 0 10 == false  -- boundary
#guard inRange 15 0 10 == false

-- Logical OR: check if a value is outside a range
def outOfRange := [Meirei|
  def outOfRange(x: Int, lo: Int, hi: Int): Bool {
    return (x < lo) || (x > hi);
  }
]

#guard outOfRange 5 0 10 == false
#guard outOfRange (-1) 0 10 == true
#guard outOfRange 11 0 10 == true

-- Logical NOT
def isOdd := [Meirei|
  def isOdd(n: Int): Bool {
    return !(n % 2 == 0);
  }
]

#guard isOdd 3 == true
#guard isOdd 4 == false
#guard isOdd 0 == false

-- Combined: inclusive range check using && with <= and >=
def inRangeInclusive := [Meirei|
  def inRangeInclusive(x: Int, lo: Int, hi: Int): Bool {
    return (x >= lo) && (x <= hi);
  }
]

#guard inRangeInclusive 5 0 10 == true
#guard inRangeInclusive 0 0 10 == true   -- boundary
#guard inRangeInclusive 10 0 10 == true  -- boundary
#guard inRangeInclusive 11 0 10 == false

-- =============================================================================
-- Compound expressions: mixing arithmetic, comparison, and logic
-- =============================================================================

-- Sum elements satisfying a modulo condition
partial def sumEvenElements := [Meirei|
  def sumEvenElements(xs: [Int]): Int {
    var total: Int = 0;
    for x in xs {
      if (x % 2 == 0) {
        total = total + x;
      }
    }
    return total;
  }
]

#guard sumEvenElements [1, 2, 3, 4, 5, 6] == 12  -- 2+4+6
#guard sumEvenElements [1, 3, 5] == 0

-- While loop with compound condition
-- Divide by 2 while even
partial def halveTillOdd := [Meirei|
  def halveTillOdd(n: Int): Int {
    var x: Int = n;
    while (x % 2 == 0) {
      x = x / 2;
    }
    return x;
  }
]

#guard halveTillOdd 16 == 1
#guard halveTillOdd 24 == 3
#guard halveTillOdd 7 == 7

-- =============================================================================
-- Boolean literals: true, false
-- =============================================================================

-- Return true/false directly
def alwaysTrue := [Meirei|
  def alwaysTrue(): Bool {
    return true;
  }
]

#guard alwaysTrue == true

-- Use boolean literals in conditional logic
def classifySign := [Meirei|
  def classifySign(n: Int): Bool {
    if (n > 0) {
      return true;
    }
    return false;
  }
]

#guard classifySign 5 == true
#guard classifySign 0 == false
#guard classifySign (-3) == false

-- Boolean literal as initial value in a loop
partial def anyPositive := [Meirei|
  def anyPositive(xs: [Int]): Bool {
    var found: Bool = false;
    for x in xs {
      if (x > 0) {
        found = true;
      }
    }
    return found;
  }
]

#guard anyPositive [(-1), (-2), 3] == true
#guard anyPositive [(-1), (-2)] == false

end ComparisonAndLogic
