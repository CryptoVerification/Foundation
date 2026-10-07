import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyInitialization

/-! Lift actual authentication stages into the whole privacy machine with
variable durations. Only the local responder absorbs after native halt;
the whole machine immediately transfers and returns the response. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false

private theorem observation_of_pure {A B : Type*} (p : PMF A) (observe : A → B) (value : B)
    (h : p.map observe = PMF.pure value) (point : A) (hPoint : point ∈ p.support) :
    observe point = value := by
  have hm : observe point ∈ (p.map observe).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨point, hPoint, rfl⟩
  rwa [h, PMF.mem_support_pure_iff] at hm

def responderBoundary (responder : ResponseHandoff.Control) : Bool :=
  (responseOutput responder).isSome

def responseBoundary (frame : Frame State) : Bool :=
  match frame.control with
  | .responding _ _ responder => responderBoundary responder
  | _ => false

def embedResponder (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool))
    (responder : ResponseHandoff.Control) : Frame State :=
  ⟨state, .responding machine request responder, sourceTrace, externalTrace⟩

theorem responder_eval_eq (fuel : Nat) (start : ResponseHandoff.Control) :
    TimedExecution.eval ResponseHandoff.step fuel start = ResponseHandoff.eval fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      simp only [TimedExecution.eval, ResponseHandoff.eval]
      congr 1
      funext next
      exact ih next

theorem responder_absorbing (responder : ResponseHandoff.Control)
    (h : responderBoundary responder = true) :
    ResponseHandoff.step responder = PMF.pure responder := by
  apply ResponseHandoff.step_terminal
  cases responder <;> simp [responderBoundary, responseOutput] at h
  rename_i key machine
  cases hh : machine.halted <;> simp [hh] at h
  simp [ResponseHandoff.publicPacket, hh]

theorem responding_until {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (fuel : Nat) (responder : ResponseHandoff.Control) :
    TimedExecution.runToBoundary (step code oracle) responseBoundary fuel
      (embedResponder machine request state sourceTrace externalTrace responder) =
      (TimedExecution.runToBoundary ResponseHandoff.step responderBoundary fuel responder).map
        (fun result => (embedResponder machine request state sourceTrace externalTrace result.1, result.2)) := by
  apply TimedExecution.runToBoundary_map
  · intro next
    rfl
  · intro next hNext
    cases ho : responseOutput next with
    | none =>
        simp only [step, embedResponder, ho]
        rfl
    | some pair => simp [responderBoundary, ho] at hNext

/-- Ordinary local output-layout proofs determine the physical output of
all stopped endpoints, despite their different actual stopping times. -/
theorem responder_endpoint (fuel : Nat) (responder : ResponseHandoff.Control)
    (storedKey output : Tape)
    (hLayout : (ResponseHandoff.eval fuel responder).map responseOutput =
      PMF.pure (some (storedKey, output)))
    (result : ResponseHandoff.Control × Nat)
    (hResult : result ∈ (TimedExecution.runToBoundary
      ResponseHandoff.step responderBoundary fuel responder).support) :
    responseOutput result.1 = some (storedKey, output) := by
  let block := TimedExecution.Block.stopped ResponseHandoff.step responderBoundary fuel responder
  have hComplete : block.Completes responderBoundary := by
    intro final hFinal
    apply TimedExecution.runToBoundary_completes ResponseHandoff.step responderBoundary fuel responder _ final hFinal
    intro point hPoint
    rw [responder_eval_eq] at hPoint
    have ho := observation_of_pure _ _ _ hLayout point hPoint
    simp [responderBoundary, ho]
  have hLaw := block.final_law (fun final hf => responder_absorbing final.1 (hComplete final hf))
    fuel (Nat.le_refl _)
  have hObs : block.outcome.map (fun final => responseOutput final.1) =
      PMF.pure (some (storedKey, output)) := by
    change block.outcome.map (responseOutput ∘ Prod.fst) = _
    rw [← PMF.map_comp]
    rw [← hLaw, responder_eval_eq]
    exact hLayout
  exact observation_of_pure _ _ _ hObs result hResult

noncomputable def responseFirst {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (fuel : Nat) (responder : ResponseHandoff.Control) :=
  TimedExecution.Block.stopped (step code oracle) responseBoundary fuel
    (embedResponder machine request state sourceTrace externalTrace responder)

theorem responseFirst_endpoint {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (fuel : Nat) (responder : ResponseHandoff.Control) (storedKey output : Tape)
    (hLayout : (ResponseHandoff.eval fuel responder).map responseOutput =
      PMF.pure (some (storedKey, output))) (result : Frame State × Nat)
    (hResult : result ∈ (responseFirst code oracle machine request state sourceTrace externalTrace fuel responder).outcome.support) :
    ∃ completed used, result = (embedResponder machine request state sourceTrace externalTrace completed, used) ∧
      responseOutput completed = some (storedKey, output) := by
  change result ∈ (TimedExecution.runToBoundary (step code oracle) responseBoundary fuel
    (embedResponder machine request state sourceTrace externalTrace responder)).support at hResult
  rw [responding_until, PMF.mem_support_map_iff] at hResult
  obtain ⟨endpoint, hEndpoint, he⟩ := hResult
  exact ⟨endpoint.1, endpoint.2, he.symm, responder_endpoint fuel responder storedKey output hLayout endpoint hEndpoint⟩

/-- One actual ownership transfer, followed by the actual cell-level return. -/
theorem completed_callback_return {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (completed : ResponseHandoff.Control) (storedKey : Tape) (key : TableMAC.Key width)
    (ciphertext : Option Bool)
    (hOutput : responseOutput completed = some (storedKey, AuthenticateResponse.responseTape key ciphertext)) :
    eval code oracle (1 + returnBudget width ciphertext)
      (embedResponder machine request state sourceTrace externalTrace completed) =
      PMF.pure ⟨state, .source storedKey (.loading machine
        (AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) {}),
        (request, AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) :: sourceTrace,
        externalTrace⟩ := by
  rw [Nat.add_comm 1, eval]
  simp only [step, embedResponder, hOutput, PMF.pure_bind]
  exact return_authentication_run code oracle storedKey key ciphertext machine request state sourceTrace externalTrace

def callbackResult {State : Type u} {width : Nat} (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (storedKey : Tape) (key : TableMAC.Key width) (ciphertext : Option Bool) : Frame State :=
  ⟨state, .source storedKey (.loading machine
      (AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) {}),
    (request, AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) :: sourceTrace,
    externalTrace⟩

noncomputable def callbackBlock {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (fuel : Nat) (responder : ResponseHandoff.Control) (ciphertext : Option Bool) :
    TimedExecution.Block (step code oracle)
      (embedResponder machine request state sourceTrace externalTrace responder) :=
  (responseFirst code oracle machine request state sourceTrace externalTrace fuel responder).compose
    (fun frame => TimedExecution.Block.fixed (step code oracle) (1 + returnBudget width ciphertext) frame)
    (1 + returnBudget width ciphertext) (by intro result hResult; exact Nat.le_refl _)

/-- Exact source-frame endpoint of the composed actual callback. The
suspended source's tapes, external state and transcript remain accounted for. -/
theorem callbackBlock_endpoint {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (fuel : Nat) (responder : ResponseHandoff.Control) (storedKey : Tape)
    (key : TableMAC.Key width) (ciphertext : Option Bool)
    (hLayout : (ResponseHandoff.eval fuel responder).map responseOutput =
      PMF.pure (some (storedKey, AuthenticateResponse.responseTape key ciphertext)))
    (result : Frame State × Nat)
    (hResult : result ∈ (callbackBlock (width := width) code oracle machine request state sourceTrace externalTrace
      fuel responder ciphertext).outcome.support) :
    result.1 = callbackResult machine request state sourceTrace externalTrace storedKey key ciphertext := by
  change result ∈ ((responseFirst code oracle machine request state sourceTrace externalTrace fuel responder).outcome.bind
    (fun middle => (TimedExecution.Block.fixed (step code oracle) (1 + returnBudget width ciphertext) middle.1).outcome.map
      (fun final => (final.1, middle.2 + final.2)))).support at hResult
  rw [PMF.mem_support_bind_iff] at hResult
  obtain ⟨middle, hMiddle, hMap⟩ := hResult
  obtain ⟨completed, used, he, hOutput⟩ := responseFirst_endpoint code oracle machine request state
    sourceTrace externalTrace fuel responder storedKey _ hLayout middle hMiddle
  subst middle
  rw [PMF.mem_support_map_iff] at hMap
  obtain ⟨final, hFinal, heFinal⟩ := hMap
  have hFixed : (TimedExecution.Block.fixed (step code oracle) (1 + returnBudget width ciphertext)
      (embedResponder machine request state sourceTrace externalTrace completed)).outcome =
      PMF.pure (callbackResult machine request state sourceTrace externalTrace storedKey key ciphertext,
        1 + returnBudget width ciphertext) := by
    change (TimedExecution.eval (step code oracle) (1 + returnBudget width ciphertext)
      (embedResponder machine request state sourceTrace externalTrace completed)).map _ = _
    rw [Timing.eval_eq, completed_callback_return code oracle machine request state sourceTrace externalTrace
      completed storedKey key ciphertext hOutput, PMF.pure_map]
    rfl
  rw [hFixed, PMF.mem_support_pure_iff] at hFinal
  subst final
  subst result
  rfl

/-- This concrete block uses the layout proof of actual native-generated
key copying and authentication; no realization is assumed. -/
noncomputable def generatedCallback {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) :=
  callbackBlock (width := width) code oracle machine request state sourceTrace externalTrace
    (ResponseHandoff.budget width ciphertext) (GeneratedResponse.initial key ciphertext) ciphertext

theorem generatedCallback_endpoint {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) (result : Frame State × Nat)
    (hResult : result ∈ (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).outcome.support) :
    result.1 = callbackResult machine request state sourceTrace externalTrace (ResponseHandoff.retainedKey key) key ciphertext :=
  callbackBlock_endpoint code oracle machine request state sourceTrace externalTrace _ _ _ key ciphertext
    (generated_completed_response key ciphertext) result hResult

theorem generatedCallback_bounded {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) (result : Frame State × Nat)
    (hResult : result ∈ (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).outcome.support) :
    result.2 ≤ 29 * width + 38 := by
  have hb := (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).bounded result hResult
  have hp := responseOverhead_le width ciphertext
  change result.2 ≤ ResponseHandoff.budget width ciphertext + (1 + returnBudget width ciphertext) at hb
  unfold responseOverhead at hp
  omega

theorem generatedCallback_completes {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).Completes
      Timing.sourceBoundary := by
  intro result hResult
  rw [generatedCallback_endpoint code oracle machine request state sourceTrace externalTrace key ciphertext result hResult]
  rfl

theorem generatedCallback_budget {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).budget =
      responseOverhead width ciphertext := by
  change ResponseHandoff.budget width ciphertext + (1 + returnBudget width ciphertext) =
    ResponseHandoff.budget width ciphertext + 1 + returnBudget width ciphertext
  omega

/-- All unused budget continues the real source machine. In particular,
this statement does not replace an early failed response with extra stutters. -/
theorem generatedCallback_law {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (ciphertext : Option Bool) (horizon : Nat)
    (hHorizon : responseOverhead width ciphertext ≤ horizon) :
    eval code oracle horizon
      (embedResponder machine request state sourceTrace externalTrace (GeneratedResponse.initial key ciphertext)) =
      (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).outcome.bind
        (fun result => eval code oracle (horizon - result.2) result.1) := by
  have h := (generatedCallback code oracle machine request state sourceTrace externalTrace key ciphertext).law horizon
    (by rw [generatedCallback_budget]; exact hHorizon)
  simpa only [Timing.eval_eq] using h

/-- One actual external query enters the callback with the same state
update and raw external transcript, decoding at most two response cells. -/
theorem generated_source_query {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) :
    step code oracle ⟨state, .source (PrivateKeyGeneration.store key) (.awaiting machine request),
      sourceTrace, externalTrace⟩ =
      (oracle state request).map (fun answer => embedResponder machine request answer.1 sourceTrace
        ((request, answer.2) :: externalTrace) (GeneratedResponse.initial key (decodeCiphertext answer.2))) := by
  simp only [step, CryptoOracle.Interactive.Reification.terminal,
    CryptoOracle.Interactive.Reification.action, CryptoOracle.Interactive.transition,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Query plus actual native callback, including adaptive state updates.
All remaining time resumes the source; the external capability costs one
transition and native signing/copying/return costs remain explicit. -/
theorem generated_query_law {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (key : TableMAC.Key width) (horizon : Nat) (hHorizon : 29 * width + 38 ≤ horizon) :
    eval code oracle (1 + horizon)
      ⟨state, .source (PrivateKeyGeneration.store key) (.awaiting machine request), sourceTrace, externalTrace⟩ =
      (oracle state request).bind (fun answer =>
        (generatedCallback code oracle machine request answer.1 sourceTrace
          ((request, answer.2) :: externalTrace) key (decodeCiphertext answer.2)).outcome.bind
            (fun result => eval code oracle (horizon - result.2) result.1)) := by
  rw [Nat.add_comm 1, eval, generated_source_query, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext answer
  exact generatedCallback_law code oracle machine request answer.1 sourceTrace
    ((request, answer.2) :: externalTrace) key (decodeCiphertext answer.2) horizon
      ((responseOverhead_le width _).trans hHorizon)

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
