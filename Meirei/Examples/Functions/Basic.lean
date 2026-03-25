/-
  Examples demonstrating the imperative language syntax

  This file shows that the grammar and expander can successfully
  compile the intSum and mySum examples to executable Lean 4 code.
-/

import Meirei.IR.Meirei.Elaborator.Index

open Meirei

-- Example 1: intSum function using term-level syntax
def intSum_example := [Meirei|
  def intSum(x: Int, y: Int): Int {
    return x + y;
  }
]

#check intSum_example
#guard intSum_example 5 3 == 8

-- Example 2: mySum function using term-level syntax
def mySum_example := [Meirei|
  def mySum(l: [Int]): Int {
    var out: Int = 0;
    for i in l {
      out = intSum_example(out, i);
    }
    return out;
  }
]

#check mySum_example
#print mySum_example
#guard mySum_example [1, 2, 3, 4, 5] == 15

-- Note: More complex patterns (multiple variables, nested loops, etc.)
-- are not yet supported by the expander. See ImperativeExpanderExamples.lean
-- for additional working examples.
