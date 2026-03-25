/-
  List Literal Examples

  Demonstrates the use of list literals in Meirei expressions,
  including as function arguments.
-/

import Meirei.IR.Meirei.Elaborator.Index

open Meirei

-- Helper function to test list literal as argument
def sumList := [Meirei|
  def sumList(l: [Int]): Int {
    var total: Int = 0;
    for x in l {
      total = total + x;
    }
    return total;
  }
]

#check sumList
#guard sumList [1, 2, 3, 4, 5] == 15

-- Test with list literal as function argument
def testListLiteral := [Meirei|
  def testListLiteral(): Int {
    return sumList([10, 20, 30]);
  }
]

#check testListLiteral
#guard testListLiteral == 60

-- Test with empty list literal
def testEmptyList := [Meirei|
  def testEmptyList(): Int {
    return sumList([]);
  }
]

#check testEmptyList
#guard testEmptyList == 0

-- Test with list literal containing single element
def testSingleElement := [Meirei|
  def testSingleElement(): Int {
    return sumList([42]);
  }
]

#check testSingleElement
#guard testSingleElement == 42

-- Test with list literal containing expressions
def testExpressions := [Meirei|
  def testExpressions(): Int {
    var x: Int = 5;
    return sumList([x, x + 1, x * 2]);
  }
]

#check testExpressions
#guard testExpressions == 21  -- 5 + 6 + 10 = 21

-- Test nested function calls with list literals
def processLists := [Meirei|
  def processLists(): Int {
    var a: Int = sumList([1, 2, 3]);
    var b: Int = sumList([4, 5]);
    return a + b;
  }
]

#check processLists
#guard processLists == 15  -- 6 + 9 = 15
