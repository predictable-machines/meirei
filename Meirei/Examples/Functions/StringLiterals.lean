/-
  String Literals — Comprehensive Tests

  Exercises string literal parsing and elaboration across every
  expression position that Meirei supports: return, var init,
  assignment, function arguments, comparisons, option wrapping,
  and combinations with structs/enums.
-/

import PredictableVerification.IR.Meirei.Index

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

#eval returnString  -- "hello world"

-- Empty string
def returnEmpty := [Meirei|
  def returnEmpty(): String {
    return "";
  }
]

#eval returnEmpty  -- ""

-- String with spaces and punctuation
def returnPunctuation := [Meirei|
  def returnPunctuation(): String {
    return "Hello, World! 123";
  }
]

#eval returnPunctuation  -- "Hello, World! 123"

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

#eval varInitPreserved []   -- "initialized"
#eval varInitPreserved [1]  -- "changed"

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

#eval varInitEmpty []   -- ""
#eval varInitEmpty [1]  -- "notempty"

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

#eval assignInLoop []   -- "none"
#eval assignInLoop [1]  -- "found"
#eval assignInLoop [1, 2, 3]  -- "found"

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

#eval makeTag 1  -- { label := "default", priority := 1 }
#eval makeTag 0  -- { label := "default", priority := 0 }

-- String argument from parameter forwarded alongside literal
def makeTagWith := [Meirei|
  def makeTagWith(name: String, p: Int): NameTag {
    return NameTag.mk(name, p);
  }
]

#eval makeTagWith "alice" 5  -- { label := "alice", priority := 5 }

-- =============================================================================
-- 5. Multiple String Fields in Struct
-- =============================================================================

meirei_type struct FullName { first: String, last: String }

def makeFullName := [Meirei|
  def makeFullName(): FullName {
    return FullName.mk("Jane", "Doe");
  }
]

#eval makeFullName  -- { first := "Jane", last := "Doe" }

-- Mix of literal and parameter strings
def makeFullNameWith := [Meirei|
  def makeFullNameWith(first: String): FullName {
    return FullName.mk(first, "Unknown");
  }
]

#eval makeFullNameWith "Alice"  -- { first := "Alice", last := "Unknown" }

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

#eval isAlice "alice"  -- 1
#eval isAlice "bob"    -- 0
#eval isAlice ""       -- 0

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

#eval matchesGreeting "hello"  -- 1
#eval matchesGreeting "hi"     -- 2
#eval matchesGreeting "hey"    -- 0

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

#check maybeGreet                  -- Int → Option String
#eval maybeGreet 1                 -- some "hello"
#eval maybeGreet 0                 -- none

-- Struct with optional string field
meirei_type struct UserProfile { name: String, nickname: String? }

def makeProfile := [Meirei|
  def makeProfile(name: String): UserProfile {
    return UserProfile.mk(name, none);
  }
]

#eval makeProfile "alice"  -- { name := "alice", nickname := none }

def makeProfileWithNick := [Meirei|
  def makeProfileWithNick(name: String, nick: String): UserProfile {
    return UserProfile.mk(name, some(nick));
  }
]

#eval makeProfileWithNick "alice" "ally"
-- { name := "alice", nickname := some "ally" }

-- =============================================================================
-- 8. String in Enum Constructors
-- =============================================================================

meirei_type enum Greeting { Hello(name: String), Goodbye(name: String), Anonymous() }

def greetAlice := [Meirei|
  def greetAlice(): Greeting {
    return Greeting.Hello("alice");
  }
]

#eval greetAlice  -- Greeting.Hello "alice"

def farewellTo := [Meirei|
  def farewellTo(name: String): Greeting {
    return Greeting.Goodbye(name);
  }
]

#eval farewellTo "bob"  -- Greeting.Goodbye "bob"

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

#eval greetingName (Greeting.Hello "alice")    -- "alice"
#eval greetingName (Greeting.Goodbye "bob")    -- "bob"
#eval greetingName Greeting.Anonymous          -- "unknown"

-- =============================================================================
-- 10. String Field Access
-- =============================================================================

def getLabel := [Meirei|
  def getLabel(tag: NameTag): String {
    return tag.label;
  }
]

#eval getLabel (NameTag.mk "urgent" 1)  -- "urgent"

def getFirst := [Meirei|
  def getFirst(name: FullName): String {
    return name.first;
  }
]

#eval getFirst (FullName.mk "Jane" "Doe")  -- "Jane"

-- =============================================================================
-- 11. String Passed Through Multiple Functions
-- =============================================================================

-- Pass string as parameter, build struct, extract via accessor
def roundTrip := [Meirei|
  def roundTrip(s: String): String {
    return getLabel(NameTag.mk(s, 0));
  }
]

#eval roundTrip "test"   -- "test"
#eval roundTrip ""       -- ""
#eval roundTrip "hello"  -- "hello"

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

#eval conditionalString 1  -- "one"
#eval conditionalString 0  -- "other"
#eval conditionalString 2  -- "other"

-- =============================================================================
-- 13. String in Nested Struct Construction
-- =============================================================================

meirei_type struct LabeledPoint { label: String, x: Int, y: Int }

def origin := [Meirei|
  def origin(): LabeledPoint {
    return LabeledPoint.mk("origin", 0, 0);
  }
]

#eval origin  -- { label := "origin", x := 0, y := 0 }

def namedPoint := [Meirei|
  def namedPoint(name: String, x: Int, y: Int): LabeledPoint {
    return LabeledPoint.mk(name, x, y);
  }
]

#eval namedPoint "A" 3 4    -- { label := "A", x := 3, y := 4 }
#eval namedPoint "B" 10 20  -- { label := "B", x := 10, y := 20 }

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

#eval hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "a"  -- 1
#eval hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "b"  -- 1
#eval hasLabelInList [NameTag.mk "a" 1, NameTag.mk "b" 2] "c"  -- 0
#eval hasLabelInList [] "a"  -- 0

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

#eval hasDefaultTag [NameTag.mk "default" 0]            -- 1
#eval hasDefaultTag [NameTag.mk "other" 1]              -- 0
#eval hasDefaultTag [NameTag.mk "a" 1, NameTag.mk "default" 0]  -- 1

-- =============================================================================
-- 15. Identity: String Parameter → String Return
-- =============================================================================

def echoString := [Meirei|
  def echoString(s: String): String {
    return s;
  }
]

#eval echoString "anything"  -- "anything"
#eval echoString ""          -- ""
#eval echoString "123"       -- "123"

end StringLiteralTests
