/-
  Algebraic Types Examples

  Demonstrates Meirei struct (product) and enum (sum) types with
  field access, constructor calls, and pattern matching.
-/

import PredictableVerification.IR.Meirei.Index

open Meirei

-- =============================================================================
-- Struct Definition (Product Type)
-- =============================================================================

meirei_type struct Point { x: Int, y: Int }

#check Point           -- Type
#check Point.mk        -- Int → Int → Point
#check @Point.x        -- Point → Int

#eval Point.mk 3 4     -- { x := 3, y := 4 }

-- =============================================================================
-- Enum Definition (Sum Type)
-- =============================================================================

meirei_type enum Shape { Circle(radius: Int), Rectangle(width: Int, height: Int) }

#check Shape                -- Type
#check Shape.Circle         -- Int → Shape
#check Shape.Rectangle      -- Int → Int → Shape

#eval Shape.Circle 5              -- Shape.Circle 5
#eval Shape.Rectangle 3 4         -- Shape.Rectangle 3 4

-- =============================================================================
-- Field Access
-- =============================================================================

def getX := [Meirei|
  def getX(p: Point): Int {
    return p.x;
  }
]

#check getX                  -- Point → Int
#eval getX (Point.mk 10 20) -- 10

def getY := [Meirei|
  def getY(p: Point): Int {
    return p.y;
  }
]

#eval getY (Point.mk 10 20) -- 20

-- =============================================================================
-- Constructor Calls
-- =============================================================================

def makeCircle := [Meirei|
  def makeCircle(r: Int): Shape {
    return Shape.Circle(r);
  }
]

#check makeCircle          -- Int → Shape
#eval makeCircle 7         -- Shape.Circle 7

def makeRect := [Meirei|
  def makeRect(w: Int, h: Int): Shape {
    return Shape.Rectangle(w, h);
  }
]

#check makeRect            -- Int → Int → Shape
#eval makeRect 3 4         -- Shape.Rectangle 3 4

-- =============================================================================
-- Pattern Matching on Enums
-- =============================================================================

def describeShape := [Meirei|
  def describeShape(s: Shape): Int {
    match s {
      case Shape.Circle(r) { return r; }
      case Shape.Rectangle(w, h) { return w + h; }
    }
  }
]

#check describeShape                         -- Shape → Int
#eval describeShape (Shape.Circle 5)         -- 5
#eval describeShape (Shape.Rectangle 3 4)    -- 7

-- =============================================================================
-- Combined: Struct + Field Access + Arithmetic
-- =============================================================================

def manhattanDistance := [Meirei|
  def manhattanDistance(p: Point): Int {
    return p.x + p.y;
  }
]

#check manhattanDistance                      -- Point → Int
#eval manhattanDistance (Point.mk 3 4)        -- 7
#eval manhattanDistance (Point.mk 10 20)      -- 30

-- =============================================================================
-- AST Printing for New Constructs
-- =============================================================================

#print_meirei_ast struct Point2 { x: Int, y: Int }

#print_meirei_ast enum Shape2 { Circle(radius: Int), Rectangle(width: Int, height: Int) }

#print_meirei_ast
  def describeShape2(s: Shape): Int {
    match s {
      case Shape.Circle(r) { return r; }
      case Shape.Rectangle(w, h) { return w + h; }
    }
  }

-- =============================================================================
-- Recursive Data Structures
-- =============================================================================

-- Binary tree: Leaf has no data, Node holds a value and two subtrees
meirei_type enum IntTree { Leaf(), Node(value: Int, left: IntTree, right: IntTree) }

#check IntTree              -- Type
#check IntTree.Leaf         -- IntTree
#check IntTree.Node         -- Int → IntTree → IntTree → IntTree

-- Build some trees by hand
#eval IntTree.Leaf
#eval IntTree.Node 1 IntTree.Leaf IntTree.Leaf
#eval IntTree.Node 10
        (IntTree.Node 5 IntTree.Leaf IntTree.Leaf)
        (IntTree.Node 15 IntTree.Leaf IntTree.Leaf)

-- =============================================================================
-- Pattern Matching on Recursive Types
-- =============================================================================

-- Check if a tree is a leaf (returns 1 for leaf, 0 for node)
def isLeaf := [Meirei|
  def isLeaf(t: IntTree): Int {
    match t {
      case IntTree.Leaf() { return 1; }
      case IntTree.Node(v, l, r) { return 0; }
    }
  }
]

#eval isLeaf IntTree.Leaf                                    -- 1
#eval isLeaf (IntTree.Node 42 IntTree.Leaf IntTree.Leaf)     -- 0

-- Extract root value (0 for leaves)
def rootValue := [Meirei|
  def rootValue(t: IntTree): Int {
    match t {
      case IntTree.Leaf() { return 0; }
      case IntTree.Node(v, l, r) { return v; }
    }
  }
]

#eval rootValue IntTree.Leaf                                 -- 0
#eval rootValue (IntTree.Node 42 IntTree.Leaf IntTree.Leaf)  -- 42

-- Construct a single-node tree from a value
def singletonTree := [Meirei|
  def singletonTree(v: Int): IntTree {
    return IntTree.Node(v, IntTree.Leaf(), IntTree.Leaf());
  }
]

#check singletonTree                                         -- Int → IntTree
#eval singletonTree 99  -- IntTree.Node 99 IntTree.Leaf IntTree.Leaf

-- Build a tree with a given root and two leaf children holding given values
def threeNodeTree := [Meirei|
  def threeNodeTree(root: Int, leftVal: Int, rightVal: Int): IntTree {
    return IntTree.Node(root,
      IntTree.Node(leftVal, IntTree.Leaf(), IntTree.Leaf()),
      IntTree.Node(rightVal, IntTree.Leaf(), IntTree.Leaf()));
  }
]

#eval threeNodeTree 10 5 15
-- IntTree.Node 10 (IntTree.Node 5 IntTree.Leaf IntTree.Leaf)
--                  (IntTree.Node 15 IntTree.Leaf IntTree.Leaf)

-- =============================================================================
-- Recursive Linked List
-- =============================================================================

meirei_type enum IntList { Nil(), Cons(head: Int, tail: IntList) }

#check IntList          -- Type
#check IntList.Nil      -- IntList
#check IntList.Cons     -- Int → IntList → IntList

#eval IntList.Cons 1 (IntList.Cons 2 (IntList.Cons 3 IntList.Nil))

-- Get the head element (0 for empty lists)
def headOrZero := [Meirei|
  def headOrZero(xs: IntList): Int {
    match xs {
      case IntList.Nil() { return 0; }
      case IntList.Cons(h, t) { return h; }
    }
  }
]

#eval headOrZero IntList.Nil                              -- 0
#eval headOrZero (IntList.Cons 42 IntList.Nil)            -- 42
#eval headOrZero (IntList.Cons 1 (IntList.Cons 2 IntList.Nil))  -- 1

-- Prepend a value to a list
def prepend := [Meirei|
  def prepend(x: Int, xs: IntList): IntList {
    return IntList.Cons(x, xs);
  }
]

#eval prepend 0 (IntList.Cons 1 (IntList.Cons 2 IntList.Nil))
-- IntList.Cons 0 (IntList.Cons 1 (IntList.Cons 2 IntList.Nil))

-- =============================================================================
-- Optional (Maybe) Type
-- =============================================================================

meirei_type enum OptionalInt { None(), Some(value: Int) }

-- Unwrap with a default
def getOrDefault := [Meirei|
  def getOrDefault(opt: OptionalInt, fallback: Int): Int {
    match opt {
      case OptionalInt.None() { return fallback; }
      case OptionalInt.Some(v) { return v; }
    }
  }
]

#eval getOrDefault OptionalInt.None 0              -- 0
#eval getOrDefault (OptionalInt.Some 42) 0         -- 42

-- Safe division: returns None on divide-by-zero
def safeDivide := [Meirei|
  def safeDivide(a: Int, b: Int): OptionalInt {
    if (b == 0) {
      return OptionalInt.None();
    } else {
      return OptionalInt.Some(a / b);
    }
  }
]

#eval safeDivide 10 3   -- OptionalInt.Some 3
#eval safeDivide 10 0   -- OptionalInt.None
