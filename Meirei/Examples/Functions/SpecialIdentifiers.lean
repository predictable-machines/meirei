/-
  Special Identifier Syntax - Question Mark and Exclamation Mark Suffixes

  This file demonstrates that Meirei supports the same identifier syntax as Lean,
  including function names ending with `?` and `!`, following Lean's convention:
  - `?` suffix: functions that return an Option
  - `!` suffix: functions that might crash or perform unsafe operations

  Tests:
  1. Function definitions with ? and ! suffixes
  2. Function calls with ? and ! suffixes
  3. Qualified names (e.g., List.isEmpty?) with special characters
  4. Field access with special characters
  5. Variable assignments with special characters
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace SpecialIdentifiers

-- =============================================================================
-- Test 1: Function Definitions with Special Suffixes
-- =============================================================================

-- Function with ? suffix (returns Option)
def isEmpty?_def := [Meirei|
  def isEmpty?(n : Int) : Bool {
    return n == 0;
  }
]

#check isEmpty?_def
-- Expected: isEmpty?_def (n : Int) : Bool

-- Function with ! suffix (unsafe operation)
def getFirst!_def := [Meirei|
  def getFirst!(nums : [Int]) : Int {
    return 42;
  }
]

#check getFirst!_def
-- Expected: getFirst!_def (nums : List Int) : Int

-- =============================================================================
-- Test 2: Calling Functions with Special Suffixes
-- =============================================================================

-- Call the previously defined isEmpty? function
def callIsEmpty := [Meirei|
  def testZero(x : Int) : Bool {
    var result: Bool = isEmpty?_def(x);
    return result;
  }
]

#check callIsEmpty
-- Expected: callIsEmpty (x : Int) : Bool

-- Call the previously defined getFirst! function
def callGetFirst := [Meirei|
  def tryGetFirst(nums : [Int]) : Int {
    var first: Int = getFirst!_def(nums);
    return first;
  }
]

#check callGetFirst
-- Expected: callGetFirst (nums : List Int) : Int

-- =============================================================================
-- Test 3: Qualified Names with Special Characters
-- =============================================================================

-- Create a helper namespace with functions that have special suffixes
namespace StringUtils
  def isEmpty? (s : String) : Bool := s.length = 0
  def assertNonEmpty! (s : String) : String :=
    if s.length > 0 then s else "DEFAULT"
end StringUtils

-- Now call these qualified names from Meirei
def useQualifiedQuestion := [Meirei|
  def checkString(text : String) : Bool {
    var empty: Bool = StringUtils.isEmpty?(text);
    return empty;
  }
]

#check useQualifiedQuestion
-- Expected: useQualifiedQuestion (text : String) : Bool

def useQualifiedExclaim := [Meirei|
  def ensureNonEmpty(text : String) : String {
    var result: String = StringUtils.assertNonEmpty!(text);
    return result;
  }
]

#check useQualifiedExclaim
-- Expected: useQualifiedExclaim (text : String) : String

-- =============================================================================
-- Test 4: Assignment with Functions Having Special Characters
-- =============================================================================

-- Demonstrates assigning results from functions with ? and ! suffixes
def multipleAssignments := [Meirei|
  def processString(s1 : String, s2 : String) : Bool {
    var check1: Bool = StringUtils.isEmpty?(s1);
    var check2: Bool = StringUtils.isEmpty?(s2);
    var result: Bool = check1 && check2;
    return result;
  }
]

#check multipleAssignments
-- Expected: multipleAssignments (s1 : String) (s2 : String) : Bool

-- Demonstrates that assignment targets themselves don't have special characters
-- (you can't declare `var result?: Int`), but you CAN assign from functions
-- with special characters to regular variables
def assignFromSpecialFunc := [Meirei|
  def checkAndTransform(x : Int, s : String) : String {
    var isZero: Bool = isEmpty?_def(x);
    var result: String = StringUtils.assertNonEmpty!(s);
    return result;
  }
]

#check assignFromSpecialFunc
-- Expected: assignFromSpecialFunc (x : Int) (s : String) : String

-- =============================================================================
-- Test 5: Logical NOT vs Exclamation in Identifiers
-- =============================================================================

-- The logical NOT operator works with or without spaces: `!b`, `! b`, or `!(b)`
-- An identifier ending with ! is written attached to the name: `isEmpty!` or `getFirst!(x)`
-- Lean's lexer disambiguates: `isEmpty!` is one token (identifier), `!isEmpty` is two tokens (operator + identifier)

def testLogicalNot := [Meirei|
  def negate(b : Bool) : Bool {
    if (!b) {
      return true;
    }
    return false;
  }
]

#check testLogicalNot
-- Expected: testLogicalNot (b : Bool) : Bool

end SpecialIdentifiers
