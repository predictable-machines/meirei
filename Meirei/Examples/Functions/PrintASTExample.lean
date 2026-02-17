/-
  Example demonstrating Meirei AST printing

  This file shows how to use the #print_meirei_ast command to inspect
  the intermediate AST representation before elaboration to Lean code.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

-- Example 1: Print AST for a simple function
#print_meirei_ast
  def add(x: Int, y: Int): Int {
    return x + y;
  }

-- Example 2: Print AST for a function with loops and state
#print_meirei_ast
  def sumList(l: [Int]): Int {
    var result: Int = 0;
    for item in l {
      result = result + item;
    }
    return result;
  }

-- Example 3: Print AST for a function with conditionals
#print_meirei_ast
  def absolute(x: Int): Int {
    if (x < 0) {
      return 0 - x;
    } else {
      return x;
    }
  }

-- Example 4: Print AST for a function with nested loops
#print_meirei_ast
  def nestedSum(outer: [Int], inner: [Int]): Int {
    var total: Int = 0;
    for i in outer {
      for j in inner {
        total = total + i + j;
      }
    }
    return total;
  }

-- Example 5: Print AST for a function with break statement
#print_meirei_ast
  def findFirst(l: [Int], target: Int): Int {
    var found: Int = -1;
    for item in l {
      if (item == target) {
        found = item;
        break;
      }
    }
    return found;
  }

-- After viewing the AST, you can still create and use the functions normally:
def myAdd := [Meirei|
  def add(x: Int, y: Int): Int {
    return x + y;
  }
]

#check myAdd
#guard myAdd 5 3 == 8
