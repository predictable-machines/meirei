/-
  Examples demonstrating the imperative language syntax

  This file shows that the grammar and expander can successfully
  compile the intSum and mySum examples to executable Lean 4 code.
-/

import PredictableVerification.IR.Meirei.Elaborator.Index

open Meirei

-- Example 1: intSum function using term-level syntax
def intSum_example := [Meirei|
  def intSum(x: int, y: int): int {
    return x + y;
  }
]

#check intSum_example  -- Should type-check as: Int → Int → Int
#eval intSum_example 5 3  -- Should evaluate to 8

-- Example 2: mySum function using term-level syntax
def mySum_example := [Meirei|
  def mySum(l: [int]): int {
    var out: int = 0;
    for i in l {
      out = intSum_example(out, i);
    }
    return out;
  }
]

#check mySum_example   -- Should type-check as: List Int → Int
#print mySum_example
#eval mySum_example [1, 2, 3, 4, 5]  -- Should evaluate to 15

-- Note: More complex patterns (multiple variables, nested loops, etc.)
-- are not yet supported by the expander. See ImperativeExpanderExamples.lean
-- for additional working examples.
