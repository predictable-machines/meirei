/-
  Qualified Names — Tests for using qualified Lean names in Meirei

  Exercises qualified name support in two positions:
  1. Function calls: `String.append(a, b)` via `ident ("." ident)*` syntax
  2. Value expressions: `Nat.zero` via field-chain detection in the elaborator
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

namespace QualifiedNameTests

-- =============================================================================
-- 1. Single-Level Qualified Names (Namespace.function)
-- =============================================================================

def natSucc := [Meirei|
  def natSucc(n: Nat): Nat {
    return Nat.succ(n);
  }
]

#guard natSucc 0 == 1
#guard natSucc 4 == 5

def natAdd := [Meirei|
  def natAdd(a: Nat, b: Nat): Nat {
    return Nat.add(a, b);
  }
]

#guard natAdd 3 4 == 7
#guard natAdd 0 0 == 0

-- =============================================================================
-- 2. Multi-Level Qualified Names (A.B.function)
-- =============================================================================

namespace Helpers.Math
def double (n : Nat) : Nat := n * 2
def triple (n : Nat) : Nat := n * 3
end Helpers.Math

def useDoublyQualified := [Meirei|
  def useDoublyQualified(n: Nat): Nat {
    return Helpers.Math.double(n);
  }
]

#guard useDoublyQualified 5 == 10
#guard useDoublyQualified 0 == 0

def useTriple := [Meirei|
  def useTriple(n: Nat): Nat {
    return Helpers.Math.triple(n);
  }
]

#guard useTriple 3 == 9

-- =============================================================================
-- 3. Qualified Names in Expressions (not just return position)
-- =============================================================================

def qualifiedInCondition := [Meirei|
  def qualifiedInCondition(n: Nat): Nat {
    if (Nat.ble(n, 5) == true) {
      return 1;
    } else {
      return 0;
    }
  }
]

#guard qualifiedInCondition 3 == 1
#guard qualifiedInCondition 5 == 1
#guard qualifiedInCondition 6 == 0

def qualifiedInVarInit := [Meirei|
  def qualifiedInVarInit(n: Nat, xs: [Nat]): Nat {
    var acc: Nat = Nat.succ(n);
    for x in xs {
      acc = Nat.add(acc, x);
    }
    return acc;
  }
]

#guard qualifiedInVarInit 0 [1, 2, 3] == 7
#guard qualifiedInVarInit 10 [] == 11

-- =============================================================================
-- 4. Qualified Names in Loops
-- =============================================================================

def qualifiedInLoop := [Meirei|
  def qualifiedInLoop(xs: [Nat]): Nat {
    var total: Nat = 0;
    for x in xs {
      total = Nat.add(total, Nat.succ(x));
    }
    return total;
  }
]

#guard qualifiedInLoop [0, 0, 0] == 3
#guard qualifiedInLoop [1, 2, 3] == 9
#guard qualifiedInLoop [] == 0

-- =============================================================================
-- 5. Mixing Qualified and Unqualified Calls
-- =============================================================================

def localHelper (n : Nat) : Nat := n + 100

def mixedCalls := [Meirei|
  def mixedCalls(n: Nat): Nat {
    var x: Nat = Nat.succ(n);
    var y: Nat = localHelper(x);
    return Nat.add(x, y);
  }
]

#guard mixedCalls 0 == 102
#guard mixedCalls 9 == 120

-- =============================================================================
-- 6. Qualified Constructor Calls (already worked, but verify no regression)
-- =============================================================================

meirei_type struct Pair { fst: Nat, snd: Nat }

def makePairQualified := [Meirei|
  def makePairQualified(a: Nat, b: Nat): Pair {
    return Pair.mk(a, b);
  }
]

#guard (makePairQualified 1 2).fst == 1
#guard (makePairQualified 1 2).snd == 2

-- =============================================================================
-- 7. Bool Qualified Functions
-- =============================================================================

def boolNot := [Meirei|
  def boolNot(b: Bool): Bool {
    return Bool.not(b);
  }
]

#guard boolNot true == false
#guard boolNot false == true

-- =============================================================================
-- 8. List Qualified Functions
-- =============================================================================

def listLength := [Meirei|
  def listLength(xs: [Nat]): Nat {
    return List.length(xs);
  }
]

#guard listLength ([] : List Nat) == 0
#guard listLength [1, 2, 3] == 3

def listReverse := [Meirei|
  def listReverse(xs: [Nat]): [Nat] {
    return List.reverse(xs);
  }
]

#guard listReverse [1, 2, 3] == [3, 2, 1]
#guard listReverse ([] : List Nat) == []

-- =============================================================================
-- 9. Qualified Values (not function calls)
-- =============================================================================

def useNatZero := [Meirei|
  def useNatZero(): Nat {
    return Nat.zero;
  }
]

#guard useNatZero == 0

namespace Constants
def magicNumber : Nat := 42
end Constants

def useQualifiedConstant := [Meirei|
  def useQualifiedConstant(): Nat {
    return Constants.magicNumber;
  }
]

#guard useQualifiedConstant == 42

-- =============================================================================
-- 10. Multi-Level Qualified Values
-- =============================================================================

namespace Outer.Inner
def value : Nat := 99
end Outer.Inner

def useDeepQualifiedValue := [Meirei|
  def useDeepQualifiedValue(): Nat {
    return Outer.Inner.value;
  }
]

#guard useDeepQualifiedValue == 99

-- =============================================================================
-- 11. Qualified Values in Expressions (not just return position)
-- =============================================================================

def qualifiedValueInArithmetic := [Meirei|
  def qualifiedValueInArithmetic(n: Nat): Nat {
    return n + Constants.magicNumber;
  }
]

#guard qualifiedValueInArithmetic 0 == 42
#guard qualifiedValueInArithmetic 8 == 50

def qualifiedValueInCondition := [Meirei|
  def qualifiedValueInCondition(n: Nat): Nat {
    if (n == Nat.zero) {
      return 1;
    } else {
      return 0;
    }
  }
]

#guard qualifiedValueInCondition 0 == 1
#guard qualifiedValueInCondition 5 == 0

def qualifiedValueInVarInit := [Meirei|
  def qualifiedValueInVarInit(xs: [Nat]): Nat {
    var acc: Nat = Constants.magicNumber;
    for x in xs {
      acc = acc + x;
    }
    return acc;
  }
]

#guard qualifiedValueInVarInit [] == 42
#guard qualifiedValueInVarInit [1, 2, 3] == 48

-- =============================================================================
-- 12. Field Access Still Works on Local Variables (regression)
-- =============================================================================

def fieldAccessRegression := [Meirei|
  def fieldAccessRegression(p: Pair): Nat {
    return p.fst + p.snd;
  }
]

#guard fieldAccessRegression (Pair.mk 3 7) == 10

-- =============================================================================
-- 13. Field Access on For-Loop Iterator Variables
-- =============================================================================
-- Previously a known limitation: `p.fst` inside a for-loop body failed because
-- Lean's tokenizer merged `p.fst` into a single ident, bypassing SSA versioning.
-- The parser now decomposes hierarchical idents into fieldAccess chains.

def sumPairFsts := [Meirei|
  def sumPairFsts(pairs: [Pair]): Nat {
    var total: Nat = 0;
    for p in pairs {
      total = total + p.fst;
    }
    return total;
  }
]

#guard sumPairFsts [] == 0
#guard sumPairFsts [Pair.mk 1 10, Pair.mk 2 20, Pair.mk 3 30] == 6

def sumPairBoth := [Meirei|
  def sumPairBoth(pairs: [Pair]): Nat {
    var total: Nat = 0;
    for p in pairs {
      total = total + p.fst + p.snd;
    }
    return total;
  }
]

#guard sumPairBoth [] == 0
#guard sumPairBoth [Pair.mk 1 10, Pair.mk 2 20] == 33

end QualifiedNameTests
