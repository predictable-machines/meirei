/-
    TranslationTypes.lean
    Types for the Translation Pipeline
    Issue #175 - Translation Pipeline Infrastructure
  -/

import Lean.Data.Json
import JsonSchema

namespace PredictableVerification.Translation

open JsonSchema

  /-- Source language for translation -/
  inductive SourceLanguage where
    | java : SourceLanguage
    | kotlin : SourceLanguage
  deriving Repr, BEq, Inhabited

  def SourceLanguage.toString : SourceLanguage → String
    | .java => "java"
    | .kotlin => "kotlin"

  instance : ToString SourceLanguage := ⟨SourceLanguage.toString⟩

  /-- Translation request input -/
  structure TranslationRequest where
    sourceCode : String
    language : SourceLanguage
    context : Option String        -- Class context, fields, etc.
    methodName : Option String     -- For tracking/logging
  deriving Repr

  /-- JSON format reminder for user prompt -/
  def jsonFormatReminder : String :=
    "IMPORTANT: Respond ONLY with a JSON object using EXACTLY these field names: " ++
    "meirei_code, confidence, approximations, notes. " ++
    "No explanatory text. No markdown. Start directly with the opening brace."

  /-- Build XML format for the LLM prompt -/
  def TranslationRequest.toXML (req : TranslationRequest) : String :=
    let contextSection := match req.context with
      | some ctx => s!"\n  <context>\n{ctx}\n  </context>"
      | none => ""
    s!"<translation_request>
  <source language=\"{req.language}\">
{req.sourceCode}
  </source>{contextSection}
</translation_request>

{jsonFormatReminder}"

  /-- Approximation type for metadata -/
  inductive ApproximationType where
    | arithmeticOverflow : ApproximationType    -- Int overflow not modeled
    | floatingPoint : ApproximationType         -- Float precision loss
    | stringOperations : ApproximationType      -- String ops simplified
    | concurrency : ApproximationType           -- Threading ignored
    | exceptions : ApproximationType            -- Exception paths simplified
    | nullability : ApproximationType           -- Null handling approximated
    | collections : ApproximationType           -- Collection bounds unchecked
    | externalCall : ApproximationType          -- External call behavior assumed
  deriving Repr, BEq

  def ApproximationType.toString : ApproximationType → String
    | .arithmeticOverflow => "arithmetic_overflow"
    | .floatingPoint => "floating_point"
    | .stringOperations => "string_operations"
    | .concurrency => "concurrency"
    | .exceptions => "exceptions"
    | .nullability => "nullability"
    | .collections => "collections"
    | .externalCall => "external_call"

  instance : ToString ApproximationType := ⟨ApproximationType.toString⟩

  /-- Severity level of an approximation's impact on verification -/
  inductive SeverityLevel where
    | low : SeverityLevel       -- Minor impact, unlikely to affect verification
    | medium : SeverityLevel    -- Moderate impact, may affect some proofs
    | high : SeverityLevel      -- Significant impact, review required
  deriving Repr, BEq

  def SeverityLevel.toNat : SeverityLevel → Nat
    | .low => 1
    | .medium => 2
    | .high => 3

  def SeverityLevel.fromNat : Nat → SeverityLevel
    | 1 => .low
    | 2 => .medium
    | _ => .high

  instance : ToString SeverityLevel where
    toString
      | .low => "low"
      | .medium => "medium"
      | .high => "high"

  /-- Detailed approximation info -/
  structure ApproximationInfo where
    type : ApproximationType
    location : Option String    -- Line/construct where approximation occurs
    description : String
    severity : SeverityLevel    -- Impact on verification
  deriving Repr

  /-- Confidence level of translation -/
  inductive ConfidenceLevel where
    | high : ConfidenceLevel      -- Direct mapping, high fidelity
    | medium : ConfidenceLevel    -- Some approximations but semantics preserved
    | low : ConfidenceLevel       -- Significant approximations, review needed
  deriving Repr, BEq

  def ConfidenceLevel.toNat : ConfidenceLevel → Nat
    | .high => 3
    | .medium => 2
    | .low => 1

  def ConfidenceLevel.fromNat : Nat → ConfidenceLevel
    | 3 => .high
    | 2 => .medium
    | _ => .low

  instance : ToString ConfidenceLevel where
    toString
      | .high => "high"
      | .medium => "medium"
      | .low => "low"

  /-- Warning from translation process -/
  structure TranslationWarning where
    code : String                 -- Warning code (e.g., "W001")
    message : String
    suggestion : Option String := none
  deriving Repr

  /-- Token usage statistics -/
  structure TokenUsage where
    inputTokens : Nat
    outputTokens : Nat
    totalTokens : Nat
  deriving Repr

  def TokenUsage.empty : TokenUsage := { inputTokens := 0, outputTokens := 0, totalTokens := 0 }

  /-- Translation result -/
  structure TranslationResult where
    meireiCode : String                     -- The translated Meirei code
    confidence : ConfidenceLevel            -- Translation confidence
    approximations : List ApproximationInfo -- Approximations made
    warnings : List TranslationWarning      -- Warnings during translation
    tokenUsage : TokenUsage := TokenUsage.empty
    model : String                          -- Model used
    rawResponse : Option String             -- Raw LLM response (for debugging)
  deriving Repr

  /-- Check if translation succeeded with acceptable quality -/
  def TranslationResult.isAcceptable (result : TranslationResult) : Bool :=
    result.confidence != ConfidenceLevel.low &&
    result.meireiCode.length > 0

  /-- Get high-severity approximations -/
  def TranslationResult.criticalApproximations (result : TranslationResult) : List ApproximationInfo :=
    result.approximations.filter (·.severity == SeverityLevel.high)

  -- ============================================================================
  -- STRUCTURED OUTPUT TYPES (for Claude JSON response)
  -- ============================================================================

  /-- Approximation as returned by Claude in JSON -/
  structure LLMApproximation where
    type : String
    location : Option String
    description : String
    severity : String
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson, HasJSONSchema

  /-- Convert LLM approximation to our internal type -/
  def LLMApproximation.toApproximationInfo (approx : LLMApproximation) : ApproximationInfo :=
    let approxType := match approx.type with
      | "arithmetic_overflow" => ApproximationType.arithmeticOverflow
      | "floating_point" => ApproximationType.floatingPoint
      | "string_operations" => ApproximationType.stringOperations
      | "concurrency" => ApproximationType.concurrency
      | "exceptions" => ApproximationType.exceptions
      | "nullability" => ApproximationType.nullability
      | "collections" => ApproximationType.collections
      | "external_call" => ApproximationType.externalCall
      | _ => ApproximationType.externalCall
    let severityLevel := match approx.severity with
      | "low" => SeverityLevel.low
      | "medium" => SeverityLevel.medium
      | "high" => SeverityLevel.high
      | _ => SeverityLevel.medium
    { type := approxType
      location := approx.location
      description := approx.description
      severity := severityLevel }

  /-- Structured response from Claude -/
  structure LLMTranslationResponse where
    meirei_code : String
    confidence : String
    approximations : List LLMApproximation
    notes : Option String
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson, HasJSONSchema

  /-- Convert LLM response to our TranslationResult -/
  def LLMTranslationResponse.toTranslationResult
      (response : LLMTranslationResponse)
      (tokenUsage : TokenUsage)
      (model : String)
      (rawResponse : Option String := none) : TranslationResult :=
    let confidence := match response.confidence with
      | "high" => ConfidenceLevel.high
      | "medium" => ConfidenceLevel.medium
      | "low" => ConfidenceLevel.low
      | _ => ConfidenceLevel.medium
    let approximations := response.approximations.map LLMApproximation.toApproximationInfo
    let warnings := match response.notes with
      | some note => [{ code := "N001", message := note, suggestion := none : TranslationWarning }]
      | none => []
    { meireiCode := response.meirei_code
      confidence := confidence
      approximations := approximations
      warnings := warnings
      tokenUsage := tokenUsage
      model := model
      rawResponse := rawResponse }

  /-- Parse JSON string to LLMTranslationResponse -/
  def parseLLMResponse (jsonStr : String) : Except String LLMTranslationResponse := do
    let json ← Lean.Json.parse jsonStr
    match Lean.FromJson.fromJson? json with
    | .ok response => .ok response
    | .error msg => .error s!"Failed to parse response: {msg}"

  /-- Get the JSON schema for LLMTranslationResponse as a string -/
  def llmTranslationResponseSchema : String :=
    (HasJSONSchema.toSchema (α := LLMTranslationResponse)).toJsonString

  /-- Translation error types -/
  inductive TranslationError where
    | llmError : String → TranslationError
    | emptyResponse : TranslationError
    | timeout : TranslationError
    | rateLimited : TranslationError
    | invalidInput : String → TranslationError
    | configError : String → TranslationError
    | parseError : String → TranslationError
  deriving Repr

  def TranslationError.toString : TranslationError → String
    | .llmError msg => s!"LLM Error: {msg}"
    | .emptyResponse => "Empty response from LLM"
    | .timeout => "Translation request timed out"
    | .rateLimited => "Rate limit exceeded"
    | .invalidInput msg => s!"Invalid input: {msg}"
    | .configError msg => s!"Configuration error: {msg}"
    | .parseError msg => s!"Parse error: {msg}"

  instance : ToString TranslationError := ⟨TranslationError.toString⟩

  /-- Result type for translation operations -/
  abbrev TranslationOutcome := Except TranslationError TranslationResult

  end PredictableVerification.Translation
