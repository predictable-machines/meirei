/-
  Imperative Language Expander Examples

  This file demonstrates the expander converting imperative syntax
  into executable Lean 4 functions using term-level syntax.
-/

import PredictableVerification.IR.Meirei.Elaborator

open Meirei

-- Example 1: intSum - Pure function
-- Input:  def intSum(x: int, y: int): int { return x + y; }
-- Output: fun (x : Int) (y : Int) => x + y
def intSum := [Meirei|
  def intSum(x: int, y: int): int {
    return x + y;
  }
]

#check intSum  -- intSum : Int → Int → Int

-- Test intSum
#eval intSum 5 3  -- 8
#eval intSum 10 (-3)  -- 7

-- Example 2: mySum - Function with loop converted to fold
-- Input:  def mySum(l: [int]): int { var out: int = 0; for i in l { out = intSum(out, i); } return out; }
-- Output: fun (l : List Int) => List.foldl (fun out i => intSum out i) 0 l
def mySum := [Meirei|
  def mySum(l: [int]): int {
    var out: int = 0;
    for i in l {
      out = intSum(out, i);
    }
    return out;
  }
]

#check mySum  -- mySum : List Int → Int

-- Test mySum
#eval mySum [1, 2, 3, 4, 5]  -- 15
#eval mySum []  -- 0
#eval mySum [10, 20, 30]  -- 60

-- Example 3: multiply - Another pure function
def multiply := [Meirei|
  def multiply(a: int, b: int): int {
    return a * b;
  }
]

#check multiply  -- multiply : Int → Int → Int
#eval multiply 6 7  -- 42
#eval multiply 12 (-2)  -- -24

-- Example 4: increment - Single parameter function
def increment := [Meirei|
  def increment(n: int): int {
    return n + 1;
  }
]

#check increment  -- increment : Int → Int
#eval increment 41  -- 42
#eval increment 0  -- 1

-- Example 5: productSum - Using multiply with a loop
def productSum := [Meirei|
  def productSum(nums: [int]): int {
    var total: int = 0;
    for n in nums {
      total = multiply(total, n);
    }
    return total;
  }
]

#check productSum  -- productSum : List Int → Int
#eval productSum [2, 3, 4]  -- 0 (because it starts from 0 * 2 * 3 * 4 = 0)

-- Let's show that the imperative syntax gets expanded to readable Lean code
#print intSum
-- def intSum : Int → Int → Int :=
-- fun x y => x + y

#print mySum
-- def mySum : List Int → Int :=
-- fun l => List.foldl (fun out i => intSum out i) 0 l

#print multiply
-- def multiply : Int → Int → Int :=
-- fun a b => a * b
