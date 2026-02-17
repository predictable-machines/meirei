/-
  While Loop Examples

  Demonstrates while loops in Meirei. While loops are elaborated to
  `let rec loop` functions that check the condition for termination.
  Use `#meirei_print <funcName>` to see the full elaborated Lean code
  including loop bodies.

  Two modes:
  - `while (cond) { ... }` — no termination proof; use `partial def`.
  - `while (cond) decreasing(expr) { ... }` — emits `termination_by`
    on the generated `let rec`, allowing `def` (not `partial`). Lean
    must be able to prove that `expr.toNat` strictly decreases. If it
    cannot, remove `decreasing(...)` and fall back to `partial def`.
-/

import PredictableVerification.IR.Meirei.Index

-- Example 1: Smallest power of 2 >= n (single variable)
partial def nextPow2 := [Meirei|
  def nextPow2(n: Int): Int {
    var result: Int = 1;
    while (result < n) {
      result = result * 2;
    }
    return result;
  }
]

#meirei_print nextPow2
#print nextPow2
#check nextPow2
#guard nextPow2 1 == 1
#guard nextPow2 5 == 8
#guard nextPow2 16 == 16
#guard nextPow2 17 == 32
#guard nextPow2 100 == 128

-- mod helper for GCD
def mod (a b : Int) : Int := a % b

-- Example 2: Euclidean GCD (two variables)
partial def gcd := [Meirei|
  def gcd(a: Int, b: Int): Int {
    var x: Int = a;
    var y: Int = b;
    while (y > 0) {
      var temp: Int = y;
      y = mod(x, y);
      x = temp;
    }
    return x;
  }
]

#meirei_print gcd
#check gcd
#guard gcd 48 18 == 6
#guard gcd 100 75 == 25
#guard gcd 17 5 == 1
#guard gcd 0 5 == 5

-- Example 3: Count digits (single variable with function call in body)
partial def countDigits := [Meirei|
  def countDigits(n: Int): Int {
    var count: Int = 0;
    var num: Int = n;
    while (num > 0) {
      num = num / 10;
      count = count + 1;
    }
    return count;
  }
]

#check countDigits
#guard countDigits 0 == 0
#guard countDigits 5 == 1
#guard countDigits 42 == 2
#guard countDigits 12345 == 5

-- =============================================================================
-- While loops with termination proofs (decreasing annotation)
-- =============================================================================

-- Example 4: Countdown with termination proof (single variable)
-- Uses `def` (not `partial def`) because termination is provable.
def countdown := [Meirei|
  def countdown(n: Int): Int {
    var x: Int = n;
    while (x > 0) decreasing(x) {
      x = x - 1;
    }
    return x;
  }
]

#meirei_print countdown
#check countdown
#guard countdown 10 == 0
#guard countdown 0 == 0
#guard countdown 5 == 0

-- Example 5: Triangular number with termination proof (two variables)
-- x strictly decreases by 1 each iteration; Lean proves this automatically.
def triangular := [Meirei|
  def triangular(n: Int): Int {
    var x: Int = n;
    var total: Int = 0;
    while (x > 0) decreasing(x) {
      total = total + x;
      x = x - 1;
    }
    return total;
  }
]

#meirei_print triangular
#check triangular
#guard triangular 5 == 15
#guard triangular 10 == 55
#guard triangular 0 == 0
#guard triangular 1 == 1

-- The following would correctly error:
--   while (typo_var < 10) { }           → "while loop body does not modify any variables"
--   while (typo_var < 10) { x = x + 1; } → "Unknown identifier 'typo_var'"
