/-
  Fibonacci Function Examples

  This file demonstrates iterative Fibonacci using the imperative language syntax.
  The iterative version uses a for loop with a pair accumulator to track the
  last two Fibonacci numbers.
-/

import PredictableVerification.IR.Meirei.Elaborator

open Meirei

-- Helper: Generate a list of n integers (for iteration)
-- This is used to iterate n times in the for loop
def range (n : Int) : List Nat :=
  if n < 0 then []
  else List.range n.toNat

/-- Iterative Fibonacci using Meirei with pair accumulator pattern -/
def fib := [Meirei|
  def fib(n: int): int {
    var a: int = 0;
    var b: int = 1;
    for i in range(n) {
      var temp: int = b;
      b = a + b;
      a = temp;
    }
    return a;
  }
]

#check fib  -- fib : Int → Int (or Int → Nat depending on elaboration)
#print fib   -- Show the elaborated form

-- Test iterative Fibonacci
#eval fib 0   -- 0
#eval fib 1   -- 1
#eval fib 2   -- 1
#eval fib 3   -- 2
#eval fib 4   -- 3
#eval fib 5   -- 5
#eval fib 6   -- 8
#eval fib 7   -- 13
#eval fib 10  -- 55
