/-
  Operator Precedence Tests

  Verifies that operator precedence and associativity are parsed correctly.
  Uses #guard to fail compilation if any assertion is wrong.

  Precedence (highest to lowest):
    75: ! (unary NOT)
    70: *, /, %
    65: +, -
    50: >, <, >=, <=, ==, !=
    35: &&
    30: ||
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace OperatorPrecedence

-- =============================================================================
-- Arithmetic precedence: * / % bind tighter than + -
-- =============================================================================

-- x + y * z should parse as x + (y * z)
def mulBeforeAdd := [Meirei|
  def mulBeforeAdd(x: Int, y: Int, z: Int): Int {
    return x + y * z;
  }
]

-- 1 + (2 * 3) = 7, NOT (1 + 2) * 3 = 9
#guard mulBeforeAdd 1 2 3 == 7

-- x - y / z should parse as x - (y / z)
def divBeforeSub := [Meirei|
  def divBeforeSub(x: Int, y: Int, z: Int): Int {
    return x - y / z;
  }
]

-- 10 - (6 / 2) = 7, NOT (10 - 6) / 2 = 2
#guard divBeforeSub 10 6 2 == 7

-- x + y % z should parse as x + (y % z)
def modBeforeAdd := [Meirei|
  def modBeforeAdd(x: Int, y: Int, z: Int): Int {
    return x + y % z;
  }
]

-- 10 + (7 % 3) = 11, NOT (10 + 7) % 3 = 2
#guard modBeforeAdd 10 7 3 == 11

-- =============================================================================
-- Left associativity: same precedence operators associate left-to-right
-- =============================================================================

-- a - b + c should parse as (a - b) + c
def leftAssocAddSub := [Meirei|
  def leftAssocAddSub(a: Int, b: Int, c: Int): Int {
    return a - b + c;
  }
]

-- (10 - 3) + 2 = 9, NOT 10 - (3 + 2) = 5
#guard leftAssocAddSub 10 3 2 == 9

-- a / b * c should parse as (a / b) * c
def leftAssocMulDiv := [Meirei|
  def leftAssocMulDiv(a: Int, b: Int, c: Int): Int {
    return a / b * c;
  }
]

-- (12 / 3) * 2 = 8, NOT 12 / (3 * 2) = 2
#guard leftAssocMulDiv 12 3 2 == 8

-- =============================================================================
-- Comparison binds tighter than logical operators
-- =============================================================================

-- x > 0 && y < 10 should parse as (x > 0) && (y < 10)
def compBeforeAnd := [Meirei|
  def compBeforeAnd(x: Int, y: Int): Bool {
    return x > 0 && y < 10;
  }
]

#guard compBeforeAnd 5 5 == true      -- (5 > 0) && (5 < 10)
#guard compBeforeAnd (-1) 5 == false  -- ((-1) > 0) && (5 < 10)
#guard compBeforeAnd 5 15 == false    -- (5 > 0) && (15 < 10)

-- x < 0 || y > 10 should parse as (x < 0) || (y > 10)
def compBeforeOr := [Meirei|
  def compBeforeOr(x: Int, y: Int): Bool {
    return x < 0 || y > 10;
  }
]

#guard compBeforeOr (-1) 5 == true   -- ((-1) < 0) || (5 > 10)
#guard compBeforeOr 5 15 == true     -- (5 < 0) || (15 > 10)
#guard compBeforeOr 5 5 == false     -- (5 < 0) || (5 > 10)

-- =============================================================================
-- && binds tighter than ||
-- =============================================================================

-- a || b && c should parse as a || (b && c)
def andBeforeOr := [Meirei|
  def andBeforeOr(x: Int, y: Int, z: Int): Bool {
    return x > 0 || y > 0 && z > 0;
  }
]

-- x=1, y=(-1), z=(-1):
--   Correct parse: (1 > 0) || (((-1) > 0) && ((-1) > 0)) = true || (false && false) = true
--   Wrong parse:   ((1 > 0) || ((-1) > 0)) && ((-1) > 0) = (true || false) && false = false
#guard andBeforeOr 1 (-1) (-1) == true

-- =============================================================================
-- Arithmetic binds tighter than comparison
-- =============================================================================

-- x + y > z should parse as (x + y) > z
def arithBeforeComp := [Meirei|
  def arithBeforeComp(x: Int, y: Int, z: Int): Bool {
    return x + y > z;
  }
]

-- (3 + 4) > 5 = 7 > 5 = true
#guard arithBeforeComp 3 4 5 == true

-- x * y == z should parse as (x * y) == z
def mulBeforeEq := [Meirei|
  def mulBeforeEq(x: Int, y: Int, z: Int): Bool {
    return x * y == z;
  }
]

#guard mulBeforeEq 3 4 12 == true   -- (3 * 4) == 12
#guard mulBeforeEq 3 4 7 == false   -- (3 * 4) == 7

-- =============================================================================
-- Unary NOT (!) has highest precedence
-- =============================================================================

-- !a && b should parse as (!a) && b
def notBeforeAnd := [Meirei|
  def notBeforeAnd(x: Int, y: Int): Bool {
    return !(x > 0) && y > 0;
  }
]

-- (!((-1) > 0)) && (1 > 0) = (!false) && true = true
#guard notBeforeAnd (-1) 1 == true
-- (!(1 > 0)) && (1 > 0) = (!true) && true = false
#guard notBeforeAnd 1 1 == false

-- =============================================================================
-- Complex expressions combining multiple precedence levels
-- =============================================================================

-- a + b * c > d && e - f < g
-- Should parse as: ((a + (b * c)) > d) && ((e - f) < g)
def complexPrecedence := [Meirei|
  def complexPrecedence(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int): Bool {
    return a + b * c > d && e - f < g;
  }
]

-- ((1 + (2 * 3)) > 5) && ((10 - 3) < 8) = (7 > 5) && (7 < 8) = true
#guard complexPrecedence 1 2 3 5 10 3 8 == true

-- ((1 + (2 * 3)) > 10) && ((10 - 3) < 8) = (7 > 10) && (7 < 8) = false
#guard complexPrecedence 1 2 3 10 10 3 8 == false

-- =============================================================================
-- Parentheses override precedence (sanity check)
-- =============================================================================

def explicitParens := [Meirei|
  def explicitParens(x: Int, y: Int, z: Int): Int {
    return (x + y) * z;
  }
]

-- (1 + 2) * 3 = 9
#guard explicitParens 1 2 3 == 9

def explicitParensLogic := [Meirei|
  def explicitParensLogic(x: Int, y: Int, z: Int): Bool {
    return (x > 0 || y > 0) && z > 0;
  }
]

-- x=1, y=(-1), z=(-1):
--   With parens: (true || false) && false = false
--   Without parens would be: true || (false && false) = true
#guard explicitParensLogic 1 (-1) (-1) == false

end OperatorPrecedence
