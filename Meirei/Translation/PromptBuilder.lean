/-
  SystemPrompt.lean
  Module for LLM translation system prompts and few-shot examples
  Issue #175 - Translation Pipeline Infrastructure
-/

import JsonSchema
import PredictableVerification.Translation.TranslationTypes

namespace PredictableVerification.Translation

open JsonSchema

/-- Full system prompt for LLM translation from Java/Kotlin to Meirei IR -/
def fullSystemPrompt : String :=
"Let's translate the given source file to Meirei IR. " ++
"Make sure to import any PredictableVerification stuff needed " ++
"for the Lean module to recognize the Meirei syntax and elaboration. " ++
"You need to do this fully autonomously, without asking for human " ++
"input at any point. This is the translation prompt:

````markdown
<system_prompt>
You are a code translator specialized in converting imperative source code to Meirei IR.

Meirei is a minimal imperative DSL embedded in Lean 4 that elaborates to pure functional code.
Your task is to translate a single source file to valid Meirei IR and produce an accompanying
approximations XML manifest that records where constructs cannot be directly translated.

<meirei_syntax>
## Types
Int                     -- Mathematical integers (unbounded)
String                  -- UTF-8 strings
Bool                    -- Boolean (true/false literals; also produced by comparison/logical ops)
[T]                     -- List of T
T?                      -- Optional T (Option type)
Except(E, T)            -- Error-or-value (Except E T in Lean)

## Type Declarations
meirei_type struct Name { field1: Type1, field2: Type2 }
meirei_type enum Name { Ctor1(field: Type), Ctor2(), Ctor3(f1: T1, f2: T2) }

## Expressions
42, -5                  -- Integer literals
\"hello\"                 -- String literals
true, false             -- Boolean literals
none                    -- Option.none
some(expr)              -- Option.some
expr.field              -- Field access
Type.mk(args)           -- Struct constructor
Type.Variant(args)      -- Enum constructor

### Qualified Names
Lean qualified names (dotted identifiers) work in two positions:

Qualified function calls:
  Nat.succ(n)           -- single-level qualified call
  String.append(s1, s2) -- call any Lean function by full name
  List.length(xs)       -- standard library functions
  Helpers.Math.double(n) -- multi-level qualified call

Qualified values (constants, zero-arg definitions):
  Nat.zero              -- qualified value, not a function call
  Constants.magicNumber -- user-defined constant
  Outer.Inner.value     -- multi-level qualified value

Qualified values can appear anywhere an expression is valid:
  return Nat.zero;
  var acc: Nat = Constants.magicNumber;
  if (n == Nat.zero) { ... }
  return n + Constants.magicNumber;

### Arithmetic operators: +, -, *, /, %
### String concatenation: ++                (concatenates String values)
### Comparison operators: >, <, >=, <=, ==, !=  (produce Bool)
### Logical operators: &&, ||, !              (operate on Bool)

All binary operators are LEFT-ASSOCIATIVE. Precedence (highest → lowest):
  !                     -- 75 (unary NOT, prefix)
  *, /, %               -- 70
  +, -                  -- 65
  ++                    -- 60 (string concatenation)
  >, <, >=, <=, ==, !=  -- 50
  &&                    -- 35
  ||                    -- 30

Examples:
  a - b + c             -- parses as (a - b) + c
  x > 0 && x < 10      -- parses as (x > 0) && (x < 10)
  total + (f(x))        -- Wrap function calls in parens as right operand of +/-
  \"Hello, \" ++ name ++ \"!\"  -- string concatenation chains left-to-right
  result ++ pre ++ word ++ post  -- multiple concatenations

## Statements
var x: Type = expr;     -- Declaration (type required)
x = expr;               -- Assignment
return expr;            -- Return
throw expr;             -- Throw exception (function must return Except(E,T) or be effectful)
result <- call();       -- Effectful binding
call();                 -- Effectful void call
for x in list { }       -- Loop over list
while (cond) { }        -- While loop
if (cond) { } else { }  -- Conditional
break;                  -- Exit for loop
match expr {            -- Pattern match
  case Type.Ctor(bindings) { }
}

## Functions
def name(p1: T1, p2: T2): ReturnT {
  statements
}

## Pattern Matching
match expr {
  case TypeName.Constructor(binding1, binding2) { statements }
  case TypeName.Constructor() { statements }
}
NOTE: Fully qualify constructors: Option.none(), Shape.Circle(r)
</meirei_syntax>

<translation_rules>
## Direct Mappings
- Integer types → Int
- List/array types → [T]
- String types → String
- String concatenation → `++` operator (e.g., `s1 ++ s2`, `\"Hello, \" ++ name ++ \"!\"`)
- For-each loops → for x in list
- if/else → if/else
- return, break → return, break

## Required Transformations
- Classes/structs → meirei_type struct + functions with self parameter
- Enums/tagged unions → meirei_type enum with variants
- Boolean types → Bool (with `true`/`false` literals, &&, ||, !)
- Instance/member methods → functions with explicit self parameter
- Field mutation → create new struct with Type.mk(...)
- Optional/nullable types → T? with match on Option.none()/Option.some(v)
- Exceptions/error handling → Use `throw` + `Except(E, T)` return type.
    Define an inductive error type capturing each distinct exception the source
    code can throw. For pure functions (no axiom calls), use Except(ErrorType, T)
    as the Meirei return type and `throw expr;` for error paths. For effectful
    functions (those with axiom calls), use EffectM ErrorType ReturnType and
    `throw` for local error cases — errors from effectful calls propagate via >>=.
    Either way the error type becomes part of the function signature so callers
    must handle it.
- Floating-point/fixed-width numeric types → Int (record in approximations XML)
- External service calls → axiom + effectful binding with <- (see <effect_modeling>)

## Critical Patterns
- Field access in loops: Direct access works (e.g., `p.fst` inside `for p in pairs`)
- Arithmetic: Always parenthesize function calls as right operand of +/-: total + (f(x))
- Boolean conditions: use comparison/logical operators or boolean literals:
  if (x > 0), if ((x > lo) && (x < hi)), var done: Bool = false;
- Validation guards: if (bad) { throw \"error\"; } before the happy path
- Comparison chains: operators are left-assoc with correct precedence, so
    x > 0 && x < 10 parses correctly as (x > 0) && (x < 10)
</translation_rules>

<effect_modeling>
IMPORTANT: Axioms are a last resort. The goal is to translate as much logic as possible
into Meirei so it can be verified. Only introduce an axiom when a call truly crosses a
system boundary that cannot be expressed in Meirei.

## When to Translate vs. When to Axiomatize

TRANSLATE as Meirei (do NOT axiomatize):
- Business logic, validation, calculations, data transformations
- Methods on domain objects (even if they are instance methods in the source)
- Helper/utility functions, even private ones
- Anything whose implementation is available in the source code

AXIOMATIZE (declare as axiom returning EffectM):
- Database / repository reads and writes
- Network calls, HTTP requests, RPC
- File system I/O
- Calls to external services or third-party SDKs
- System clock, random number generation
- Any call whose implementation is outside the source code being translated

If in doubt, translate. An axiom hides logic from verification — every axiom is a
gap the verifier cannot reason about. Prefer more Meirei code and fewer axioms.

## Pure Exception Handling (Except + throw)

For functions that can fail but have NO external/effectful calls, use the
`Except(E, T)` return type directly in Meirei. This keeps the function pure
and fully verifiable — no axioms, no `noncomputable`.

- `throw expr;` elaborates to `Except.error expr`
- `return expr;` elaborates to `Except.ok expr`

### Simple validation
```lean
def validate := [Meirei|
  def validate(x: Int): Except(String, Int) {
    if (x < 0) { throw \"negative\"; }
    return x;
  }
]
```

### Multiple guards with computation
```lean
def safeDivMod := [Meirei|
  def safeDivMod(a: Int, b: Int): Except(String, Int) {
    if (b == 0) { throw \"division by zero\"; }
    var q: Int = a / b;
    var r: Int = a % b;
    if (q == 0) { throw \"quotient is zero\"; }
    return q + r;
  }
]
```

### Throw in loops (Except fold)
When a for loop body contains `throw` and the function returns `Except(E, T)`,
the loop uses an Except fold strategy — the accumulator is `Except E AccType`
and the loop short-circuits on error:

```lean
def sumPositive := [Meirei|
  def sumPositive(nums: [Int]): Except(String, Int) {
    var total: Int = 0;
    for x in nums {
      if (x < 0) { throw \"negative found\"; }
      total = total + x;
    }
    return total;
  }
]
```

### Using custom error types
Define an inductive error type for the function's failure modes:

```lean
inductive WithdrawError where
  | insufficientFunds : WithdrawError
  | invalidAmount : WithdrawError

def withdraw := [Meirei|
  def withdraw(balance: Int, amount: Int): Except(WithdrawError, Int) {
    if (amount <= 0) { throw WithdrawError.invalidAmount; }
    if (amount > balance) { throw WithdrawError.insufficientFunds; }
    return balance - amount;
  }
]
```

NOTE: Pure Except functions do NOT need `noncomputable` — they are fully computable.

## EffectM

`EffectM` is an abbreviation for the `Except` monad:

```lean
abbrev EffectM (ε : Type) (α : Type) := Except ε α
```

- `ε` is the error type (what the call can fail with)
- `α` is the success type (what the call returns on success)
- A result is either `.ok a` (success) or `.error e` (failure)

For operations that cannot fail, use `Empty` as the error type:
```lean
abbrev EffectMNoError (α : Type) := EffectM Empty α
```

## Declaring Effectful Axioms

Every external/side-effecting call used in a Meirei function must be declared as a
Lean `axiom` BEFORE the `[Meirei| ... ]` block that calls it. Axiom declarations are
plain Lean — they go outside the quoter.

### Syntax
```lean
axiom functionName : ParamType₁ → ParamType₂ → EffectM ErrorType ReturnType
```

### Examples
```lean
-- Database / repository calls
axiom findAccountById : String → EffectM DbError Account
axiom saveAccount : Account → EffectM DbError Unit

-- Service calls with no meaningful error type
axiom getCurrentTimestamp : Unit → EffectM Empty Int

-- Operations that can fail with a domain error
inductive TransferError where
  | insufficientFunds : TransferError
  | accountNotFound : String → TransferError

axiom executeTransfer : String → String → Int → EffectM TransferError Unit
```

## Using Effectful Calls in Meirei

Inside `[Meirei| ... ]`, effectful axioms are invoked with the `<-` binding syntax.
The elaborator transforms these into monadic `>>=` (bind) chains over `EffectM`.

```lean
-- Bind the result to a variable
result <- findAccountById(id);

-- Fire-and-forget (result discarded)
saveAccount(updated);
```

## Effectful + Throw (Combined)

When a function uses both effectful binds (`<-`) and `throw`, the two compose.
Each effectful axiom carries its own error type. The caller's error type is
typically a sum type wrapping each sub-error plus local throw cases:

```lean
inductive ProcessOrderError where
  | fetchAmount : FetchAmountError → ProcessOrderError
  | invalidAmount : ProcessOrderError
  deriving Repr

abbrev EffectM (ε : Type) (α : Type) := Except ε α

def fetchAmount (orderId : Int) : EffectM ProcessOrderError Int :=
  if orderId == 0 then .error (.fetchAmount .orderNotFound) else .ok (orderId - 3)

-- Effectful binds set monadic mode: throw generates monadic throw,
-- return generates pure. Errors from helpers propagate via >>=.
def processOrder := [Meirei|
  def processOrder(orderId: Int): Int {
    amount <- fetchAmount(orderId);
    if (amount <= 0) { throw ProcessOrderError.invalidAmount; }
    return amount;
  }
]
```

Note: in effectful+throw functions, the Meirei return type is the success type
(e.g. `Int`), not `Except(...)`. The monadic type is inferred from the `<-` binds.

## Module Layout Pattern

Declare axioms at the top of the namespace, then define functions that use them:

```lean
import PredictableVerification.IR.Meirei.Index

open Meirei

namespace TranslatedCode.AccountService

-- Error types (if needed)
inductive DbError where
  | notFound : String → DbError
  | connectionFailed : DbError"

/-- Compact system prompt for simpler translations -/
def compactSystemPrompt : String :=
"Translate Java/Kotlin to Meirei IR. Output only code, no comments.
Use: let x := expr, if/then/else, match/with, let r <- external().
Types: Int for numbers/bools, Option T for nullable, String, List T.
Classes become structs. All external calls need effect binding (<-)."

/-- Minimal system prompt for basic cases -/
def minimalSystemPrompt : String :=
"Convert to Meirei IR. Pure code only. Effect bind (<-) external calls."

/-- Prompt verbosity levels -/
inductive PromptLevel where
  | full : PromptLevel
  | compact : PromptLevel
  | minimal : PromptLevel
deriving Repr, BEq

/-- Get system prompt by level -/
def getSystemPrompt (level : PromptLevel) : String :=
  match level with
  | PromptLevel.full => fullSystemPrompt
  | PromptLevel.compact => compactSystemPrompt
  | PromptLevel.minimal => minimalSystemPrompt

-- ============================================================================
-- FEW-SHOT EXAMPLES
-- ============================================================================

/-- Structure for a few-shot example -/
structure FewShotExample where
  name : String
  description : String
  input : String
  output : String
deriving Repr

/-- Example 1: Effectful operations with external calls -/
def exampleEffectful : FewShotExample := {
  name := "effectful_transfer"
  description := "Bank transfer with external service calls and effect bindings"
  input := "<translation_request>
  <source language=\"java\">
    public TransferResult transfer(String fromAccount, String toAccount, BigDecimal amount) {
        Account source = accountRepository.findById(fromAccount);
        if (source == null) {
            return TransferResult.failure(\"Source account not found\");
        }
        Account target = accountRepository.findById(toAccount);
        if (target == null) {
            return TransferResult.failure(\"Target account not found\");
        }
        if (source.getBalance().compareTo(amount) < 0) {
            return TransferResult.failure(\"Insufficient funds\");
        }
        source.withdraw(amount);
        target.deposit(amount);
        accountRepository.save(source);
        accountRepository.save(target);
        return TransferResult.success();
    }
  </source>
  <context>
    class TransferService {
        private AccountRepository accountRepository;
    }
  </context>
  <external_calls>
    Account findById(String id);
    void save(Account account);
  </external_calls>
</translation_request>"
  output := "structure TransferResult where
  success : Int
  message : String

def transfer (fromAccount : String) (toAccount : String) (amount : Int) : TransferResult :=
  let source <- accountRepository.findById(fromAccount)
  match source with
  | Option.none() => { success := 0, message := \"Source account not found\" }
  | Option.some(srcAcc) =>
    let target <- accountRepository.findById(toAccount)
    match target with
    | Option.none() => { success := 0, message := \"Target account not found\" }
    | Option.some(tgtAcc) =>
      if srcAcc.balance < amount then
        { success := 0, message := \"Insufficient funds\" }
      else
        let newSrcBalance := srcAcc.balance - amount
        let newTgtBalance := tgtAcc.balance + amount
        let srcUpdated := { srcAcc with balance := newSrcBalance }
        let tgtUpdated := { tgtAcc with balance := newTgtBalance }
        let _ <- accountRepository.save(srcUpdated)
        let _ <- accountRepository.save(tgtUpdated)
        { success := 1, message := \"\" }"
}

/-- Example 2: Optional/nullable handling -/
def exampleOptional : FewShotExample := {
  name := "optional_handling"
  description := "Method with Optional return type and null checks"
  input := "<translation_request>
  <source language=\"java\">
    public Optional<User> findActiveUser(String email) {
        User user = userRepository.findByEmail(email);
        if (user == null) {
            return Optional.empty();
        }
        if (!user.isActive()) {
            return Optional.empty();
        }
        return Optional.of(user);
    }
  </source>
  <context>
    class UserService {
        private UserRepository userRepository;
    }
  </context>
  <external_calls>
    User findByEmail(String email);
  </external_calls>
</translation_request>"
  output := "structure User where
  id : String
  email : String
  active : Int

def findActiveUser (email : String) : Option User :=
  let userResult <- userRepository.findByEmail(email)
  match userResult with
  | Option.none() => Option.none()
  | Option.some(user) =>
    if user.active = 0 then
      Option.none()
    else
      Option.some(user)"
}

/-- Example 3: Class to struct transformation -/
def exampleClassToStruct : FewShotExample := {
  name := "class_to_struct"
  description := "Java class with fields and methods transformed to Meirei struct"
  input := "<translation_request>
  <source language=\"java\">
    public class BankAccount {
        private String accountId;
        private String ownerName;
        private long balance;
        private boolean active;

        public boolean canWithdraw(long amount) {
            return active && balance >= amount;
        }

        public BankAccount withdraw(long amount) {
            if (!canWithdraw(amount)) {
                return this;
            }
            return new BankAccount(accountId, ownerName, balance - amount, active);
        }
    }
  </source>
  <context>
    // Immutable value class pattern
  </context>
  <external_calls>
    // No external calls - pure computation
  </external_calls>
</translation_request>"
  output := "structure BankAccount where
  accountId : String
  ownerName : String
  balance : Int
  active : Int

def canWithdraw (account : BankAccount) (amount : Int) : Int :=
  if account.active = 1 then
    if account.balance >= amount then 1 else 0
  else
    0

def withdraw (account : BankAccount) (amount : Int) : BankAccount :=
  let canDo := canWithdraw account amount
  if canDo = 0 then
    account
  else
    { account with balance := account.balance - amount }"
}

/-- Collection of all few-shot examples -/
def allExamples : List FewShotExample := [
  exampleEffectful,
  exampleOptional,
  exampleClassToStruct
]

/-- Format a single example for the prompt -/
def formatExample (ex : FewShotExample) : String :=
  s!"<example>
<input>
{ex.input}
</input>
<output>
{ex.output}
</output>
</example>"

/-- Build the few-shot section from selected examples -/
def buildFewShotSection (examples : List FewShotExample) : String :=
  let formatted := examples.map formatExample
  let joined := String.intercalate "\n\n" formatted
  s!"## Few-Shot Examples

The following examples demonstrate the expected translation patterns:

{joined}"

/-- Build complete prompt with system prompt and few-shot examples -/
def buildCompletePrompt (level : PromptLevel) (examples : List FewShotExample) : String :=
  let systemPrompt := getSystemPrompt level
  let fewShotSection := buildFewShotSection examples
  s!"{systemPrompt}

{fewShotSection}"

/-- Get default complete prompt (full level with all examples) -/
def defaultCompletePrompt : String :=
  buildCompletePrompt PromptLevel.full allExamples

-- ============================================================================
-- PROMPT SELECTION HELPERS
-- ============================================================================

/-- Complexity indicators for automatic prompt level selection -/
structure ComplexityIndicators where
  hasExternalCalls : Bool
  hasOptionals : Bool
  hasCollections : Bool
  hasNestedConditions : Bool
  methodCount : Nat
deriving Repr

/-- Automatically select prompt level based on complexity -/
def selectPromptLevel (indicators : ComplexityIndicators) : PromptLevel :=
  let complexityScore :=
    (if indicators.hasExternalCalls then 2 else 0) +
    (if indicators.hasOptionals then 1 else 0) +
    (if indicators.hasCollections then 1 else 0) +
    (if indicators.hasNestedConditions then 1 else 0) +
    indicators.methodCount
  if complexityScore >= 4 then
    PromptLevel.full
  else if complexityScore >= 2 then
    PromptLevel.compact
  else
    PromptLevel.minimal

/-- Select relevant examples based on code characteristics -/
def selectRelevantExamples (indicators : ComplexityIndicators) : List FewShotExample := Id.run do
  let mut selected : List FewShotExample := []
  if indicators.hasExternalCalls then
    selected := exampleEffectful :: selected
  if indicators.hasOptionals then
    selected := exampleOptional :: selected
  if indicators.methodCount > 1 then
    selected := exampleClassToStruct :: selected
  -- Always include at least one example
  if selected.isEmpty then
    [exampleClassToStruct]
  else
    selected

-- ============================================================================
-- STRUCTURED OUTPUT FORMAT
-- ============================================================================

/-- JSON schema for Claude's structured output (auto-generated from LLMTranslationResponse type) -/
def jsonOutputSchema : String :=
  llmTranslationResponseSchema

/-- Instructions for structured JSON output -/
def structuredOutputInstructions : String :=
"
## Output Format

You MUST respond with a valid JSON object. Do NOT include any text before or after the JSON.
Do NOT wrap the JSON in markdown code blocks.

The JSON must have this exact structure:
```json
{
  \"meirei_code\": \"<the translated Meirei IR code as a string>\",
  \"confidence\": \"high\" | \"medium\" | \"low\",
  \"approximations\": [
    {
      \"type\": \"<approximation_type>\",
      \"location\": \"<optional: where in source>\",
      \"description\": \"<what was approximated>\",
      \"severity\": \"low\" | \"medium\" | \"high\"
    }
  ],
  \"notes\": \"<optional: any additional notes>\"
}
```

### Confidence Levels
- **high**: Direct semantic mapping, no significant approximations
- **medium**: Some approximations but core semantics preserved
- **low**: Significant approximations, manual review recommended

### Approximation Types
- **arithmetic_overflow**: Int overflow not modeled (source uses bounded integers)
- **floating_point**: Float/double converted to Int
- **string_operations**: Complex string ops simplified
- **concurrency**: Threading/synchronization not modeled
- **exceptions**: Exception paths simplified
- **nullability**: Null handling approximated
- **collections**: Collection bounds not checked
- **external_call**: External call behavior assumed

### Example Response
```json
{
  \"meirei_code\": \"def add (a : Int) (b : Int) : Int := a + b\",
  \"confidence\": \"high\",
  \"approximations\": [],
  \"notes\": null
}
```
"

/-- Build prompt with structured output instructions -/
def buildStructuredPrompt (level : PromptLevel) (examples : List FewShotExample) : String :=
  let basePrompt := getSystemPrompt level
  let fewShotSection := buildFewShotSection examples
  s!"{basePrompt}

{structuredOutputInstructions}

{fewShotSection}"

/-- Default structured prompt -/
def defaultStructuredPrompt : String :=
  buildStructuredPrompt PromptLevel.full allExamples

end PredictableVerification.Translation
