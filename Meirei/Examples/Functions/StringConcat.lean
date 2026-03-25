/-
  String Concatenation — Tests for the `++` operator

  The `++` operator desugars to Lean's `HAppend.hAppend`, which for
  `String` is `String.append`.
-/

import Meirei.IR.Meirei.Index

open Meirei

namespace StringConcatTests

-- =============================================================================
-- 1. Basic Concatenation
-- =============================================================================

def concatTwo := [Meirei|
  def concatTwo(a: String, b: String): String {
    return a ++ b;
  }
]

#guard concatTwo "hello" " world" == "hello world"
#guard concatTwo "" "x" == "x"
#guard concatTwo "x" "" == "x"
#guard concatTwo "" "" == ""

-- =============================================================================
-- 2. Concatenation with String Literals
-- =============================================================================

def greet := [Meirei|
  def greet(name: String): String {
    return "Hello, " ++ name ++ "!";
  }
]

#guard greet "Alice" == "Hello, Alice!"
#guard greet "" == "Hello, !"

-- =============================================================================
-- 3. Concatenation in Variable Init and Loop
-- =============================================================================

def joinAll := [Meirei|
  def joinAll(words: [String]): String {
    var result: String = "";
    for w in words {
      result = result ++ w;
    }
    return result;
  }
]

#guard joinAll [] == ""
#guard joinAll ["a"] == "a"
#guard joinAll ["a", "b", "c"] == "abc"

-- =============================================================================
-- 4. Concatenation with Separator (single mutable var)
-- =============================================================================

def wrapAll := [Meirei|
  def wrapAll(words: [String], pre: String, post: String): String {
    var result: String = "";
    for w in words {
      result = result ++ pre ++ w ++ post;
    }
    return result;
  }
]

#guard wrapAll ["a", "b"] "[" "]" == "[a][b]"
#guard wrapAll [] "<" ">" == ""
#guard wrapAll ["x"] "(" ")" == "(x)"

-- =============================================================================
-- 5. Concatenation in Conditionals
-- =============================================================================

def labelValue := [Meirei|
  def labelValue(label: String, positive: Bool): String {
    if (positive == true) {
      return label ++ ": yes";
    } else {
      return label ++ ": no";
    }
  }
]

#guard labelValue "active" true == "active: yes"
#guard labelValue "active" false == "active: no"

-- =============================================================================
-- 6. Mixed with String.append (qualified call)
-- =============================================================================

def mixedConcat := [Meirei|
  def mixedConcat(a: String, b: String, c: String): String {
    return a ++ String.append(b, c);
  }
]

#guard mixedConcat "1" "2" "3" == "123"

end StringConcatTests
