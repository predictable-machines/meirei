/-
  TranslationAgent.lean
  Agent for translating Java/Kotlin code to Meirei IR using Claude

  Uses FlowProviderAdapter for LLM interaction.
  Returns structured JSON output with code and metadata.
-/

import Batteries.Data.String.Matcher
import PredictableAgents.Provider.ClaudeCLI
import PredictableAgents.Agent.Metadata
import PredictableCore.Shared.Index
import PredictableVerification.Translation.PromptBuilder
import PredictableVerification.Translation.TranslationTypes
import JsonSchema

namespace PredictableVerification.Translation

open Agents.Provider Agents.Provider.ClaudeCLI Agents.Parameters
open Agents.Agent
open PredictableCore.Shared
open JsonSchema

/-- Configuration for the TranslationAgent -/
structure TranslationAgentConfig where
  model : String
  maxTokens : Nat
  temperature : Float
  maxRetries : Nat
  timeoutMs : Nat
  verbose : Bool
  promptLevel : PromptLevel
  includeFewShot : Bool

/-- Default configuration -/
def TranslationAgentConfig.default : TranslationAgentConfig := {
  model := "claude-sonnet-4-20250514"
  maxTokens := 4096
  temperature := 0.0
  maxRetries := 3
  timeoutMs := 120000
  verbose := false
  promptLevel := .full
  includeFewShot := true
}

/-- The TranslationAgent wraps FlowProviderAdapter for code translation -/
structure TranslationAgent where
  config : TranslationAgentConfig
  systemPrompt : String

/-- Create a new TranslationAgent with structured output prompt -/
def TranslationAgent.create (config : TranslationAgentConfig := .default) : TranslationAgent :=
  let systemPrompt := if config.includeFewShot then
    buildStructuredPrompt config.promptLevel allExamples
  else
    getSystemPrompt config.promptLevel ++ structuredOutputInstructions

  { config := config, systemPrompt := systemPrompt }

/-- Create with custom system prompt -/
def TranslationAgent.createWithPrompt
    (prompt : String)
    (config : TranslationAgentConfig := .default)
    : TranslationAgent :=
  { config := config, systemPrompt := prompt }

/-- Translate source code to Meirei IR -/
def TranslationAgent.translate (agent : TranslationAgent) (request : TranslationRequest) : IO TranslationOutcome := do
  -- Validate input
  if request.sourceCode.trimAscii.toString.isEmpty then
    return .error (.invalidInput "Source code is empty")

  -- Build the prompt with XML-formatted request
  let userPrompt := request.toXML

  if agent.config.verbose then
    IO.println s!"[TranslationAgent] Translating {request.methodName.getD "unnamed"} method"
    IO.println s!"[TranslationAgent] Source language: {request.language}"
    IO.println s!"[TranslationAgent] Input length: {request.sourceCode.length} chars"

  -- Configure the adapter
  let providerConfig : ProviderConfig := {
    ProviderConfig.default with
    model := agent.config.model
    maxTurns := some 1
  }
  let agentConfig : AgentRequestConfig := {
    config := providerConfig
    params := RequestParameters.default
    logTargets := if agent.config.verbose then
      [{ target := .console, level := .debug }]
    else
      [{ target := .console, level := .error }]
    colorEnabled := true
    basePath := ""
  }

  let adapter := createFlowAdapter agentConfig

  -- Call the LLM via FlowProviderAdapter using singleRequestStructured
  try
    match ← adapter.singleRequestStructured
        (α := LLMTranslationResponse)
        agent.systemPrompt
        userPrompt with
    | .error e =>
      if agent.config.verbose then
        IO.println s!"[TranslationAgent] Provider error: {e}"
      return .error (.llmError (toString e))
    | .ok flow =>
      let result ← flow.awaitResult
      let state ← flow.currentState
      match result with
      | .error e =>
        return .error (.llmError e)
      | .ok llmResponse =>
        let agentMeta := state.metadata
        let tokenUsage : TokenUsage := {
          inputTokens := agentMeta.inputTokens
          outputTokens := agentMeta.outputTokens
          totalTokens := agentMeta.totalTokens
        }

        let translationResult := llmResponse.toTranslationResult tokenUsage agent.config.model none

        if agent.config.verbose then
          IO.println s!"[TranslationAgent] Translation complete"
          IO.println s!"[TranslationAgent] Output length: {translationResult.meireiCode.length} chars"
          IO.println s!"[TranslationAgent] Confidence: {translationResult.confidence}"
          IO.println s!"[TranslationAgent] Approximations: {translationResult.approximations.length}"
          IO.println s!"[TranslationAgent] Tokens: {tokenUsage.totalTokens}"

        return .ok translationResult

  catch e =>
    let errorMsg := toString e
    if errorMsg.containsSubstr "timeout" then
      return .error .timeout
    else if errorMsg.containsSubstr "rate" then
      return .error .rateLimited
    else
      return .error (.llmError errorMsg)

/-- Translate with retry logic -/
def TranslationAgent.translateWithRetry
    (agent : TranslationAgent)
    (request : TranslationRequest)
    : IO TranslationOutcome := do
  let mut lastError : TranslationError := .emptyResponse

  for _ in [:agent.config.maxRetries] do
    match ← agent.translate request with
    | .ok result => return .ok result
    | .error e =>
      lastError := e
      -- Retry on transient errors
      match e with
      | .timeout | .rateLimited | .llmError _ =>
        if agent.config.verbose then
          IO.println s!"[TranslationAgent] Retry due to: {e}"
        IO.sleep 1000
      | _ => return .error e

  return .error lastError

/-- Convenience method: translate from string directly -/
def TranslationAgent.translateCode
    (agent : TranslationAgent)
    (code : String)
    (language : SourceLanguage := .java) : IO TranslationOutcome := do
  let request : TranslationRequest := {
    sourceCode := code
    language := language
    context := none
    methodName := none
  }
  agent.translateWithRetry request

/-- Convenience method: translate Java code -/
def TranslationAgent.translateJava (agent : TranslationAgent) (code : String) : IO TranslationOutcome :=
  agent.translateCode code .java

/-- Convenience method: translate Kotlin code -/
def TranslationAgent.translateKotlin (agent : TranslationAgent) (code : String) : IO TranslationOutcome :=
  agent.translateCode code .kotlin

end PredictableVerification.Translation
