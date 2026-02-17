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

#check Point
#check Point.mk
#check @Point.x

#guard Point.mk 3 4 == Point.mk 3 4

-- =============================================================================
-- Enum Definition (Sum Type)
-- =============================================================================

meirei_type enum Shape { Circle(radius: Int), Rectangle(width: Int, height: Int) }

#check Shape
#check Shape.Circle
#check Shape.Rectangle

#guard Shape.Circle 5 == Shape.Circle 5
#guard Shape.Rectangle 3 4 == Shape.Rectangle 3 4

-- =============================================================================
-- Field Access
-- =============================================================================

def getX := [Meirei|
  def getX(p: Point): Int {
    return p.x;
  }
]

#check getX
#guard getX (Point.mk 10 20) == 10

def getY := [Meirei|
  def getY(p: Point): Int {
    return p.y;
  }
]

#guard getY (Point.mk 10 20) == 20

-- =============================================================================
-- Constructor Calls
-- =============================================================================

def makeCircle := [Meirei|
  def makeCircle(r: Int): Shape {
    return Shape.Circle(r);
  }
]

#check makeCircle
#guard makeCircle 7 == Shape.Circle 7

def makeRect := [Meirei|
  def makeRect(w: Int, h: Int): Shape {
    return Shape.Rectangle(w, h);
  }
]

#check makeRect
#guard makeRect 3 4 == Shape.Rectangle 3 4

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

#check describeShape
#guard describeShape (Shape.Circle 5) == 5
#guard describeShape (Shape.Rectangle 3 4) == 7

-- =============================================================================
-- Combined: Struct + Field Access + Arithmetic
-- =============================================================================

def manhattanDistance := [Meirei|
  def manhattanDistance(p: Point): Int {
    return p.x + p.y;
  }
]

#check manhattanDistance
#guard manhattanDistance (Point.mk 3 4) == 7
#guard manhattanDistance (Point.mk 10 20) == 30

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

#check IntTree
#check IntTree.Leaf
#check IntTree.Node

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

#guard isLeaf IntTree.Leaf == 1
#guard isLeaf (IntTree.Node 42 IntTree.Leaf IntTree.Leaf) == 0

-- Extract root value (0 for leaves)
def rootValue := [Meirei|
  def rootValue(t: IntTree): Int {
    match t {
      case IntTree.Leaf() { return 0; }
      case IntTree.Node(v, l, r) { return v; }
    }
  }
]

#guard rootValue IntTree.Leaf == 0
#guard rootValue (IntTree.Node 42 IntTree.Leaf IntTree.Leaf) == 42

-- Construct a single-node tree from a value
def singletonTree := [Meirei|
  def singletonTree(v: Int): IntTree {
    return IntTree.Node(v, IntTree.Leaf(), IntTree.Leaf());
  }
]

#check singletonTree
#guard singletonTree 99 == IntTree.Node 99 IntTree.Leaf IntTree.Leaf

-- Build a tree with a given root and two leaf children holding given values
def threeNodeTree := [Meirei|
  def threeNodeTree(root: Int, leftVal: Int, rightVal: Int): IntTree {
    return IntTree.Node(root,
      IntTree.Node(leftVal, IntTree.Leaf(), IntTree.Leaf()),
      IntTree.Node(rightVal, IntTree.Leaf(), IntTree.Leaf()));
  }
]

#guard threeNodeTree 10 5 15 ==
  IntTree.Node 10
    (IntTree.Node 5 IntTree.Leaf IntTree.Leaf)
    (IntTree.Node 15 IntTree.Leaf IntTree.Leaf)

-- =============================================================================
-- Recursive Linked List
-- =============================================================================

meirei_type enum IntList { Nil(), Cons(head: Int, tail: IntList) }

#check IntList
#check IntList.Nil
#check IntList.Cons

-- Get the head element (0 for empty lists)
def headOrZero := [Meirei|
  def headOrZero(xs: IntList): Int {
    match xs {
      case IntList.Nil() { return 0; }
      case IntList.Cons(h, t) { return h; }
    }
  }
]

#guard headOrZero IntList.Nil == 0
#guard headOrZero (IntList.Cons 42 IntList.Nil) == 42
#guard headOrZero (IntList.Cons 1 (IntList.Cons 2 IntList.Nil)) == 1

-- Prepend a value to a list
def prepend := [Meirei|
  def prepend(x: Int, xs: IntList): IntList {
    return IntList.Cons(x, xs);
  }
]

#guard prepend 0 (IntList.Cons 1 (IntList.Cons 2 IntList.Nil)) ==
  IntList.Cons 0 (IntList.Cons 1 (IntList.Cons 2 IntList.Nil))

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

#guard getOrDefault OptionalInt.None 0 == 0
#guard getOrDefault (OptionalInt.Some 42) 0 == 42

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

#guard safeDivide 10 3 == OptionalInt.Some 3
#guard safeDivide 10 0 == OptionalInt.None
