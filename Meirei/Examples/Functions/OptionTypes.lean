/-
  Option Types Examples

  Demonstrates Meirei's Kotlin-style option type syntax (Int?, Shape?)
  which elaborates to Lean's built-in Option type. Lean's none/some
  notation works naturally in expressions; pattern matching uses the
  qualified Option.none()/Option.some(v) constructor syntax.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace OptionTypeExamples

-- =============================================================================
-- Returning Optional Values
-- =============================================================================

def safeDivide := [Meirei|
  def safeDivide(a: Int, b: Int): Int? {
    if (b == 0) {
      return none;
    } else {
      return some(a / b);
    }
  }
]

#check safeDivide
#guard safeDivide 10 3 == some 3
#guard safeDivide 10 0 == none

-- =============================================================================
-- Option in Struct Fields
-- =============================================================================

meirei_type struct PersonRecord { age: Int, score: Int? }

#check PersonRecord
#check PersonRecord.mk

-- =============================================================================
-- Pattern Matching on Option Parameters
-- =============================================================================

def getOrZero := [Meirei|
  def getOrZero(opt: Int?): Int {
    match opt {
      case Option.none() { return 0; }
      case Option.some(v) { return v; }
    }
  }
]

#check getOrZero
#guard getOrZero Option.none == 0
#guard getOrZero (Option.some 42) == 42

-- =============================================================================
-- AST Representation
-- =============================================================================

#print_meirei_ast
  def showOpt(x: Int?, y: [Int]?): Int {
    return 0;
  }

end OptionTypeExamples
