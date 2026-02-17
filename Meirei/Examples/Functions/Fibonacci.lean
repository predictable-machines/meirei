/-
  Fibonacci Function Examples

  This file demonstrates iterative Fibonacci using the imperative language syntax.
  The iterative version uses a for loop with a pair accumulator to track the
  last two Fibonacci numbers.
-/

import PredictableVerification.IR.Meirei.Elaborator.Index

open Meirei

-- Helper: Generate a list of n integers (for iteration)
-- This is used to iterate n times in the for loop
def range (n : Int) : List Nat :=
  if n < 0 then []
  else List.range n.toNat

/-- Iterative Fibonacci using Meirei with pair accumulator pattern -/
def fib := [Meirei|
  def fib(n: Int): Int {
    var a: Int = 0;
    var b: Int = 1;
    for i in range(n) {
      var temp: Int = b;
      b = a + b;
      a = temp;
    }
    return a;
  }
]

#check fib
#print fib

#guard fib 0 == 0
#guard fib 1 == 1
#guard fib 2 == 1
#guard fib 3 == 2
#guard fib 4 == 3
#guard fib 5 == 5
#guard fib 6 == 8
#guard fib 7 == 13
#guard fib 10 == 55
