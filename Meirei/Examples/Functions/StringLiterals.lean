/-
  String Literals — Comprehensive Tests

  Exercises string literal parsing and elaboration across every
  expression position that Meirei supports: return, var init,
  assignment, function arguments, comparisons, option wrapping,
  and combinations with structs/enums.
-/

import Meirei.IR.Meirei.Index

open Meirei

namespace StringLiteralTests

-- =============================================================================
-- 1. Return Position
-- =============================================================================

def returnString := [Meirei|
  def returnString(): String {
    return "hello world";
  }
]

#guard returnString == "hello world"

-- Empty string
def returnEmpty := [Meirei|
  def returnEmpty(): String {
    return "";
  }
]

#guard returnEmpty == ""

-- String with spaces and punctuation
def returnPunctuation := [Meirei|
  def returnPunctuation(): String {
    return "Hello, World! 123";
  }
]

#guard returnPunctuation == "Hello, World! 123"

-- =============================================================================
-- 2. Variable Initialization (var requires a loop to be useful)
-- =============================================================================

-- String var init preserved when loop body doesn't execute
def varInitPreserved := [Meirei|
  def varInitPreserved(xs: [Int]): String {
    var s: String = "initialized";
    for x in xs {
      s = "changed";
    }
    return s;
  }
]

#guard varInitPreserved [] == "initialized"
#guard varInitPreserved [1] == "changed"

-- Empty string as var initializer
def varInitEmpty := [Meirei|
  def varInitEmpty(xs: [Int]): String {
    var s: String = "";
    for x in xs {
      s = "notempty";
    }
    return s;
  }
]

#guard varInitEmpty [] == ""
#guard varInitEmpty [1] == "notempty"

-- =============================================================================
-- 3. Variable Assignment in Loop
-- =============================================================================

def assignInLoop := [Meirei|
  def assignInLoop(xs: [Int]): String {
    var result: String = "none";
    for x in xs {
      result = "found";
    }
    return result;
  }
]

#guard assignInLoop [] == "none"
#guard assignInLoop [1] == "found"
#guard assignInLoop [1, 2, 3] == "found"

-- =============================================================================
-- 4. String as Function Argument (Constructor Calls)
-- =============================================================================

meirei_type struct NameTag { label: String, priority: Int }

-- Single string argument
def makeTag := [Meirei|
  def makeTag(p: Int): NameTag {
    return NameTag.mk("default", p);
  }
]

#guard makeTag 1 == NameTag.mk "default" 1
#guard makeTag 0 == NameTag.mk "default" 0

-- String argument from parameter forwarded alongside literal
def makeTagWith := [Meirei|
  def makeTagWith(name: String, p: Int): NameTag {
    return NameTag.mk(name, p);
  }
]

#guard makeTagWith "alice" 5 == NameTag.mk "alice" 5

-- =============================================================================
-- 5. Multiple String Fields in Struct
-- =============================================================================

meirei_type struct FullName { first: String, last: String }

def makeFullName := [Meirei|
  def makeFullName(): FullName {
    return FullName.mk("Jane", "Doe");
  }
]

#guard makeFullName == FullName.mk "Jane" "Doe"

-- Mix of literal and parameter strings
def makeFullNameWith := [Meirei|
  def makeFullNameWith(first: String): FullName {
    return FullName.mk(first, "Unknown");
  }
]

#guard makeFullNameWith "Alice" == FullName.mk "Alice" "Unknown"

-- =============================================================================
-- 6. String Comparison (==)
-- =============================================================================

def isAlice := [Meirei|
  def isAlice(name: String): Int {
    if (name == "alice") {
      return 1;
    } else {
      return 0;
    }
  }
]

#guard isAlice "alice" == 1
#guard isAlice "bob" == 0
#guard isAlice "" == 0

-- Compare two positions: parameter vs literal on both sides
def matchesGreeting := [Meirei|
  def matchesGreeting(s: String): Int {
    if (s == "hello") {
      return 1;
    } else {
      if (s == "hi") {
        return 2;
      } else {
        return 0;
      }
    }
  }
]

#guard matchesGreeting "hello" == 1
#guard matchesGreeting "hi" == 2
#guard matchesGreeting "hey" == 0

-- =============================================================================
-- 7. String with Option Types
-- =============================================================================

-- Return optional string
def maybeGreet := [Meirei|
  def maybeGreet(greet: Int): String? {
    if (greet == 1) {
      return some("hello");
    } else {
      return none;
    }
  }
]

#check maybeGreet
#guard maybeGreet 1 == some "hello"
#guard maybeGreet 0 == none

-- Struct with optional string field
meirei_type struct UserProfile { name: String, nickname: String? }

def makeProfile := [Meirei|
  def makeProfile(name: String): UserProfile {
    return UserProfile.mk(name, none);
  }
]

#guard makeProfile "alice" == UserProfile.mk "alice" none

def makeProfileWithNick := [Meirei|
  def makeProfileWithNick(name: String, nick: String): UserProfile {
    return UserProfile.mk(name, some(nick));
  }
]

#guard makeProfileWithNick "alice" "ally" == UserProfile.mk "alice" (some "ally")

-- =============================================================================
-- 8. String in Enum Constructors
-- =============================================================================

meirei_type enum Greeting { Hello(name: String), Goodbye(name: String), Anonymous() }

def greetAlice := [Meirei|
  def greetAlice(): Greeting {
    return Greeting.Hello("alice");
  }
]

#guard greetAlice == Greeting.Hello "alice"

def farewellTo := [Meirei|
  def farewellTo(name: String): Greeting {
    return Greeting.Goodbye(name);
  }
]

#guard farewellTo "bob" == Greeting.Goodbye "bob"

-- =============================================================================
-- 9. Pattern Matching with String Fields
-- =============================================================================

-- Extract the name from a Greeting enum
def greetingName := [Meirei|
  def greetingName(g: Greeting): String {
    match g {
      case Greeting.Hello(n) { return n; }
      case Greeting.Goodbye(n) { return n; }
      case Greeting.Anonymous() { return "unknown"; }
    }
  }
]

#guard greetingName (Greeting.Hello "alice") == "alice"
#guard greetingName (Greeting.Goodbye "bob") == "bob"
#guard greetingName Greeting.Anonymous == "unknown"

-- =============================================================================
-- 10. String Field Access
-- =============================================================================

def getLabel := [Meirei|
  def getLabel(tag: NameTag): String {
    return tag.label;
  }
]

#guard getLabel (NameTag.mk "urgent" 1) == "urgent"

def getFirst := [Meirei|
  def getFirst(name: FullName): String {
    return name.first;
  }
]

#guard getFirst (FullName.mk "Jane" "Doe") == "Jane"

-- =============================================================================
-- 11. String Passed Through Multiple Functions
-- =============================================================================

-- Pass string as parameter, build struct, extract via accessor
def roundTrip := [Meirei|
  def roundTrip(s: String): String {
    return getLabel(NameTag.mk(s, 0));
  }
]

#guard roundTrip "test" == "test"
#guard roundTrip "" == ""
#guard roundTrip "hello" == "hello"

-- =============================================================================
-- 12. String in Conditional Assignment
-- =============================================================================

def conditionalString := [Meirei|
  def conditionalString(flag: Int): String {
    if (flag == 1) {
      return "one";
    } else {
      return "other";
    }
  }
]

#guard conditionalString 1 == "one"
#guard conditionalString 0 == "other"
#guard conditionalString 2 == "other"

-- =============================================================================
-- 13. String in Nested Struct Construction
-- =============================================================================

meirei_type struct LabeledPoint { label: String, x: Int, y: Int }

def origin := [Meirei|
  def origin(): LabeledPoint {
    return LabeledPoint.mk("origin", 0, 0);
  }
]

#guard origin == LabeledPoint.mk "origin" 0 0

def namedPoint := [Meirei|
  def namedPoint(name: String, x: Int, y: Int): LabeledPoint {
    return LabeledPoint.mk(name, x, y);
  }
]

#guard namedPoint "A" 3 4 == LabeledPoint.mk "A" 3 4
#guard namedPoint "B" 10 20 == LabeledPoint.mk "B" 10 20

-- =============================================================================
-- 14. String Equality Across Field Access
-- =============================================================================

-- Helper to extract label from NameTag (field access on params works)
def tagLabel := [Meirei|
  def tagLabel(tag: NameTag): String {
    return tag.label;
  }
]

-- Check if a tag has a given label using accessor function in loop
def hasLabelInList := [Meirei|
  def hasLabelInList(tags: [NameTag], target: String): Int {
    for t in tags {
      if (tagLabel(t) == target) {
        return 1;
      }
    }
    return 0;
  }
]

#guard hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "a" == 1
#guard hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "b" == 1
#guard hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "c" == 0
#guard hasLabelInList [] "a" == 0

-- Search for a literal string in a list of tags
def hasDefaultTag := [Meirei|
  def hasDefaultTag(tags: [NameTag]): Int {
    for t in tags {
      if (tagLabel(t) == "default") {
        return 1;
      }
    }
    return 0;
  }
]

#guard hasDefaultTag [NameTag.mk "default" 0] == 1
#guard hasDefaultTag [NameTag.mk "other" 1] == 0
#guard hasDefaultTag [NameTag.mk "a" 1, NameTag.mk "default" 0] == 1

-- =============================================================================
-- 15. Identity: String Parameter → String Return
-- =============================================================================

def echoString := [Meirei|
  def echoString(s: String): String {
    return s;
  }
]

#guard echoString "anything" == "anything"
#guard echoString "" == ""
#guard echoString "123" == "123"

end StringLiteralTests
