/-
  Mutability — Var outside loops

  Tests that `var` declarations, assignments, and if/else branching
  work correctly outside of `for` loops.  Previously these patterns
  failed because the elaborator emitted bare names instead of the
  versioned `_0` / `_1` identifiers produced by addVar / updateVar.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace MutabilityTests

-- =============================================================================
-- 1. Simple var + return (Bug 1 regression)
-- =============================================================================

def varReturn := [Meirei|
  def varReturn(): String {
    var s: String = "hello";
    return s;
  }
]

#eval varReturn  -- "hello"

def varReturnInt := [Meirei|
  def varReturnInt(): Int {
    var n: Int = 42;
    return n;
  }
]

#eval varReturnInt  -- 42

-- =============================================================================
-- 2. Sequential var + assign + return
-- =============================================================================

def varAssignReturn := [Meirei|
  def varAssignReturn(): String {
    var s: String = "hello";
    s = "world";
    return s;
  }
]

#eval varAssignReturn  -- "world"

def varAssignReturnInt := [Meirei|
  def varAssignReturnInt(): Int {
    var n: Int = 0;
    n = 99;
    return n;
  }
]

#eval varAssignReturnInt  -- 99

-- =============================================================================
-- 3. Multiple sequential assignments
-- =============================================================================

def varMultiAssign := [Meirei|
  def varMultiAssign(): Int {
    var n: Int = 1;
    n = 2;
    n = 3;
    return n;
  }
]

#eval varMultiAssign  -- 3

-- =============================================================================
-- 4. If/else var propagation (Bug 2)
-- =============================================================================

def varIfElse := [Meirei|
  def varIfElse(flag: Int): String {
    var s: String = "init";
    if (flag == 1) {
      s = "one";
    } else {
      s = "other";
    }
    return s;
  }
]

#eval varIfElse 1  -- "one"
#eval varIfElse 0  -- "other"
#eval varIfElse 2  -- "other"

def varIfElseInt := [Meirei|
  def varIfElseInt(flag: Int): Int {
    var n: Int = 0;
    if (flag == 1) {
      n = 100;
    } else {
      n = 200;
    }
    return n;
  }
]

#eval varIfElseInt 1  -- 100
#eval varIfElseInt 0  -- 200

-- =============================================================================
-- 5. If-then (no else) var propagation
-- =============================================================================

def varIfThen := [Meirei|
  def varIfThen(flag: Int): String {
    var s: String = "default";
    if (flag == 1) {
      s = "changed";
    }
    return s;
  }
]

#eval varIfThen 1  -- "changed"
#eval varIfThen 0  -- "default"

-- =============================================================================
-- 6. Var + if/else still works inside loops (regression check)
-- =============================================================================

def varInLoop := [Meirei|
  def varInLoop(xs: [Int]): Int {
    var total: Int = 0;
    for x in xs {
      if (x > 0) {
        total = total + x;
      } else {
        total = total;
      }
    }
    return total;
  }
]

#eval varInLoop []         -- 0
#eval varInLoop [1, 2, 3]  -- 6
#eval varInLoop [1, -1, 2] -- 3

-- =============================================================================
-- 7. Var init + loop (existing behaviour preserved)
-- =============================================================================

def varInitLoop := [Meirei|
  def varInitLoop(xs: [Int]): String {
    var s: String = "empty";
    for x in xs {
      s = "notempty";
    }
    return s;
  }
]

#eval varInitLoop []   -- "empty"
#eval varInitLoop [1]  -- "notempty"

end MutabilityTests
