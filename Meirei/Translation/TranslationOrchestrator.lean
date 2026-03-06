/-
  TranslationOrchestrator.lean
  Orchestrator for managing batch translations of Java/Kotlin code to Meirei IR

  Coordinates multiple TranslationAgent calls with configurable strategies.
-/

import PredictableVerification.Translation.TranslationTypes
import PredictableVerification.Translation.TranslationAgent

namespace PredictableVerification.Translation

-- ============================================================================
-- ORCHESTRATION STRATEGY
-- ============================================================================

/-- Strategy for orchestrating multiple translations -/
inductive OrchestrationStrategy where
  | sequential : OrchestrationStrategy
      -- Translate one by one in order. Simple and predictable.
  | parallel : OrchestrationStrategy
      -- Translate multiple files concurrently. Faster but uses more resources.
  | dependencyAware : OrchestrationStrategy
      -- Analyze dependencies and translate in topological order.
  | adaptive : OrchestrationStrategy
      -- Start sequential, switch to parallel if no dependencies detected.

/-- Convert strategy to string for logging -/
def OrchestrationStrategy.toString : OrchestrationStrategy → String
  | .sequential => "sequential"
  | .parallel => "parallel"
  | .dependencyAware => "dependency-aware"
  | .adaptive => "adaptive"

instance : ToString OrchestrationStrategy := ⟨OrchestrationStrategy.toString⟩

-- ============================================================================
-- ORCHESTRATOR CONFIGURATION
-- ============================================================================

/-- Configuration for the TranslationOrchestrator -/
structure OrchestratorConfig where
  strategy : OrchestrationStrategy
  agentConfig : TranslationAgentConfig
  stopOnError : Bool
  maxConcurrent : Nat
  verbose : Bool

/-- Default orchestrator configuration -/
def OrchestratorConfig.default : OrchestratorConfig := {
  strategy := .sequential
  agentConfig := TranslationAgentConfig.default
  stopOnError := false
  maxConcurrent := 4
  verbose := false
}

-- ============================================================================
-- BATCH TYPES
-- ============================================================================

/-- Result of translating a single item in a batch -/
structure BatchItemResult where
  request : TranslationRequest
  outcome : TranslationOutcome
  index : Nat

/-- Check if a batch item succeeded -/
def BatchItemResult.isSuccess (item : BatchItemResult) : Bool :=
  match item.outcome with
  | .ok _ => true
  | .error _ => false

/-- Get the translation result if successful -/
def BatchItemResult.getResult? (item : BatchItemResult) : Option TranslationResult :=
  match item.outcome with
  | .ok result => some result
  | .error _ => none

/-- Get the error if failed -/
def BatchItemResult.getError? (item : BatchItemResult) : Option TranslationError :=
  match item.outcome with
  | .ok _ => none
  | .error err => some err

/-- Summary statistics for a batch translation -/
structure BatchSummary where
  totalRequests : Nat
  successCount : Nat
  failureCount : Nat
  totalInputTokens : Nat
  totalOutputTokens : Nat
  averageConfidence : Option Float

/-- Compute summary from batch results -/
def BatchSummary.fromResults (results : List BatchItemResult) : BatchSummary :=
  let successes := results.filter BatchItemResult.isSuccess
  let failures := results.filter (not ∘ BatchItemResult.isSuccess)

  let tokenStats := successes.foldl (fun (inTok, outTok) item =>
    match item.getResult? with
    | some r => (inTok + r.tokenUsage.inputTokens, outTok + r.tokenUsage.outputTokens)
    | none => (inTok, outTok)
  ) (0, 0)

  let confidenceSum := successes.foldl (fun acc item =>
    match item.getResult? with
    | some r => acc + r.confidence.toNat.toFloat
    | none => acc
  ) 0.0

  let avgConfidence := if successes.isEmpty then none
    else some (confidenceSum / successes.length.toFloat)

  {
    totalRequests := results.length
    successCount := successes.length
    failureCount := failures.length
    totalInputTokens := tokenStats.1
    totalOutputTokens := tokenStats.2
    averageConfidence := avgConfidence
  }

/-- Result of a batch translation operation -/
structure BatchResult where
  results : List BatchItemResult
  summary : BatchSummary

/-- Check if all translations in batch succeeded -/
def BatchResult.allSucceeded (batch : BatchResult) : Bool :=
  batch.summary.failureCount == 0

/-- Get all successful translations -/
def BatchResult.successes (batch : BatchResult) : List TranslationResult :=
  batch.results.filterMap BatchItemResult.getResult?

/-- Get all failed translations with their original requests -/
def BatchResult.failures (batch : BatchResult) : List (TranslationRequest × TranslationError) :=
  batch.results.filterMap (fun item =>
    match item.getError? with
    | some err => some (item.request, err)
    | none => none
  )

-- ============================================================================
-- ORCHESTRATOR
-- ============================================================================

/-- The TranslationOrchestrator manages batch translations -/
structure TranslationOrchestrator where
  config : OrchestratorConfig
  agent : TranslationAgent

/-- Create a new TranslationOrchestrator -/
def TranslationOrchestrator.create (config : OrchestratorConfig := .default) : TranslationOrchestrator :=
  let agent := TranslationAgent.create config.agentConfig
  { config := config, agent := agent }

/-- Create with custom agent -/
def TranslationOrchestrator.createWithAgent
    (agent : TranslationAgent)
    (config : OrchestratorConfig := .default) : TranslationOrchestrator :=
  { config := config, agent := agent }

-- ============================================================================
-- STRATEGY IMPLEMENTATIONS
-- ============================================================================

/-- Sequential translation: one by one in order -/
private def translateSequential
    (orchestrator : TranslationOrchestrator)
    (requests : List TranslationRequest) : IO BatchResult := do
  let mut results : List BatchItemResult := []
  let mut index := 0

  for request in requests do
    if orchestrator.config.verbose then
      let name := request.methodName.getD s!"request_{index}"
      IO.println s!"[Orchestrator] Translating {index + 1}/{requests.length}: {name}"

    let outcome ← orchestrator.agent.translateWithRetry request

    let itemResult : BatchItemResult := {
      request := request
      outcome := outcome
      index := index
    }

    results := results ++ [itemResult]

    -- Check if we should stop on error
    if orchestrator.config.stopOnError then
      match outcome with
      | .error err =>
        if orchestrator.config.verbose then
          IO.println s!"[Orchestrator] Stopping due to error: {err}"
        break
      | .ok _ => pure ()

    index := index + 1

  let summary := BatchSummary.fromResults results

  if orchestrator.config.verbose then
    IO.println s!"[Orchestrator] Batch complete: {summary.successCount}/{summary.totalRequests} succeeded"

  return { results := results, summary := summary }

/-- Parallel translation: placeholder for future implementation -/
private def translateParallel
    (orchestrator : TranslationOrchestrator)
    (requests : List TranslationRequest) : IO BatchResult := do
  -- TODO: Implement parallel translation using Task.spawn
  -- For now, fall back to sequential
  if orchestrator.config.verbose then
    IO.println "[Orchestrator] Parallel strategy not yet implemented, using sequential"
  translateSequential orchestrator requests

/-- Dependency-aware translation: placeholder for future implementation -/
private def translateDependencyAware
    (orchestrator : TranslationOrchestrator)
    (requests : List TranslationRequest) : IO BatchResult := do
  -- TODO: Implement dependency analysis and topological sort
  -- For now, fall back to sequential
  if orchestrator.config.verbose then
    IO.println "[Orchestrator] Dependency-aware strategy not yet implemented, using sequential"
  translateSequential orchestrator requests

/-- Adaptive translation: placeholder for future implementation -/
private def translateAdaptive
    (orchestrator : TranslationOrchestrator)
    (requests : List TranslationRequest) : IO BatchResult := do
  -- TODO: Implement adaptive strategy selection
  -- For now, fall back to sequential
  if orchestrator.config.verbose then
    IO.println "[Orchestrator] Adaptive strategy not yet implemented, using sequential"
  translateSequential orchestrator requests

-- ============================================================================
-- PUBLIC API
-- ============================================================================

/-- Translate a batch of requests using the configured strategy -/
def TranslationOrchestrator.translateBatch
    (orchestrator : TranslationOrchestrator)
    (requests : List TranslationRequest) : IO BatchResult := do
  if requests.isEmpty then
    return {
      results := []
      summary := {
        totalRequests := 0
        successCount := 0
        failureCount := 0
        totalInputTokens := 0
        totalOutputTokens := 0
        averageConfidence := none
      }
    }

  if orchestrator.config.verbose then
    IO.println s!"[Orchestrator] Starting batch translation of {requests.length} requests"
    IO.println s!"[Orchestrator] Strategy: {orchestrator.config.strategy}"

  match orchestrator.config.strategy with
  | .sequential => translateSequential orchestrator requests
  | .parallel => translateParallel orchestrator requests
  | .dependencyAware => translateDependencyAware orchestrator requests
  | .adaptive => translateAdaptive orchestrator requests

/-- Translate a single request (convenience method) -/
def TranslationOrchestrator.translate
    (orchestrator : TranslationOrchestrator)
    (request : TranslationRequest) : IO TranslationOutcome :=
  orchestrator.agent.translateWithRetry request

/-- Translate multiple source code strings (convenience method) -/
def TranslationOrchestrator.translateCodes
    (orchestrator : TranslationOrchestrator)
    (codes : List String)
    (language : SourceLanguage := .java) : IO BatchResult := do
  let requests := codes.mapIdx (fun idx code => {
    sourceCode := code
    language := language
    context := none
    methodName := some s!"method_{idx}"
  })
  orchestrator.translateBatch requests

-- ============================================================================
-- REPORTING
-- ============================================================================

/-- Generate a text report from batch results -/
def BatchResult.toReport (batch : BatchResult) : String :=
  let header := "=== Translation Batch Report ==="
  let summary := s!"Total: {batch.summary.totalRequests} | Success: {batch.summary.successCount} | Failed: {batch.summary.failureCount}"
  let tokens := s!"Tokens: {batch.summary.totalInputTokens} in / {batch.summary.totalOutputTokens} out"
  let confidence := match batch.summary.averageConfidence with
    | some c => s!"Average Confidence: {c}"
    | none => "Average Confidence: N/A"

  let failures := if batch.summary.failureCount > 0 then
    let failureLines := batch.failures.map (fun (req, err) =>
      let name := req.methodName.getD "unnamed"
      s!"  - {name}: {err}"
    )
    "\nFailures:\n" ++ String.intercalate "\n" failureLines
  else
    ""

  s!"{header}\n{summary}\n{tokens}\n{confidence}{failures}"

/-- Print batch report to stdout -/
def BatchResult.printReport (batch : BatchResult) : IO Unit :=
  IO.println batch.toReport

end PredictableVerification.Translation
