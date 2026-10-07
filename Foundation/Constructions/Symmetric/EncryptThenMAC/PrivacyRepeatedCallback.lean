import Foundation.Constructions.Symmetric.EncryptThenMAC.RetainedResponse

/-! A query theorem closed under the private store layouts produced by
initialization and by previous queries. Layout is a proof index, not a
runtime instruction or an extra secret-key generation operation. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false

inductive StoreLayout where
  | generated
  | retained
  deriving DecidableEq, Repr

def StoreLayout.tape {width : Nat} (layout : StoreLayout) (key : TableMAC.Key width) : Tape :=
  match layout with
  | .generated => PrivateKeyGeneration.store key
  | .retained => ResponseHandoff.retainedKey key

def StoreLayout.responder {width : Nat} (layout : StoreLayout) (key : TableMAC.Key width)
    (ciphertext : Option Bool) : ResponseHandoff.Control :=
  .headerWriting (layout.tape key) (ResponseHandoff.header ciphertext) {}

theorem StoreLayout.completed_response {width : Nat} (layout : StoreLayout)
    (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval (ResponseHandoff.budget width ciphertext) (layout.responder key ciphertext)).map
      responseOutput = PMF.pure (some (ResponseHandoff.retainedKey key,
        AuthenticateResponse.responseTape key ciphertext)) := by
  cases layout with
  | generated => exact generated_completed_response key ciphertext
  | retained => exact RetainedResponse.completed_response key ciphertext

noncomputable def storedCallback {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) :=
  callbackBlock (width := width) code oracle machine request state sourceTrace externalTrace
    (ResponseHandoff.budget width ciphertext) (layout.responder key ciphertext) ciphertext

/-- Both initial and repeated queries restore precisely the retained layout
of this same key. No fresh key is sampled by the callback. -/
theorem storedCallback_endpoint {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) (result : Frame State × Nat)
    (hResult : result ∈ (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.support) :
    result.1 = callbackResult machine request state sourceTrace externalTrace
      (StoreLayout.retained.tape key) key ciphertext :=
  callbackBlock_endpoint code oracle machine request state sourceTrace externalTrace _ _ _ key ciphertext
    (layout.completed_response key ciphertext) result hResult

/-- The complete observable resumed state has the prescribed distribution,
independently of the callback's actual duration. -/
theorem storedCallback_result_distribution {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.map Prod.fst =
      PMF.pure (callbackResult machine request state sourceTrace externalTrace
        (StoreLayout.retained.tape key) key ciphertext) := by
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind]
  calc
    _ = (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.bindOnSupport
      (fun _ _ => PMF.pure (callbackResult machine request state sourceTrace externalTrace
        (StoreLayout.retained.tape key) key ciphertext)) := by
      congr 1
      funext result hResult
      change PMF.pure result.1 = _
      rw [storedCallback_endpoint code oracle machine request state sourceTrace externalTrace layout key ciphertext result hResult]
    _ = _ := by rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

theorem storedCallback_budget {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).budget =
      responseOverhead width ciphertext := by
  change ResponseHandoff.budget width ciphertext + (1 + returnBudget width ciphertext) =
    ResponseHandoff.budget width ciphertext + 1 + returnBudget width ciphertext
  omega

theorem storedCallback_bounded {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) (result : Frame State × Nat)
    (hResult : result ∈ (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.support) :
    result.2 ≤ 29 * width + 38 := by
  have hb := (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).bounded result hResult
  rw [storedCallback_budget] at hb
  exact hb.trans (responseOverhead_le width ciphertext)

theorem storedCallback_completes {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).Completes
      Timing.sourceBoundary := by
  intro result hResult
  rw [storedCallback_endpoint code oracle machine request state sourceTrace externalTrace layout key ciphertext result hResult]
  rfl

theorem storedCallback_law {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) (horizon : Nat)
    (hHorizon : responseOverhead width ciphertext ≤ horizon) :
    eval code oracle horizon
      (embedResponder machine request state sourceTrace externalTrace (layout.responder key ciphertext)) =
      (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.bind
        (fun result => eval code oracle (horizon - result.2) result.1) := by
  have h := (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).law horizon
    (by rw [storedCallback_budget]; exact hHorizon)
  simpa only [Timing.eval_eq] using h

theorem stored_source_query {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) :
    step code oracle ⟨state, .source (layout.tape key) (.awaiting machine request), sourceTrace, externalTrace⟩ =
      (oracle state request).map (fun answer => embedResponder machine request answer.1 sourceTrace
        ((request, answer.2) :: externalTrace) (layout.responder key (decodeCiphertext answer.2))) := by
  simp only [step, CryptoOracle.Interactive.Reification.terminal,
    CryptoOracle.Interactive.Reification.action, CryptoOracle.Interactive.transition,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The same query law applies after any previous callback, since it always
returns the retained layout. The continuation may make further queries. -/
theorem stored_query_law {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (horizon : Nat) (hHorizon : 29 * width + 38 ≤ horizon) :
    eval code oracle (1 + horizon)
      ⟨state, .source (layout.tape key) (.awaiting machine request), sourceTrace, externalTrace⟩ =
      (oracle state request).bind (fun answer =>
        (storedCallback code oracle machine request answer.1 sourceTrace
          ((request, answer.2) :: externalTrace) layout key (decodeCiphertext answer.2)).outcome.bind
            (fun result => eval code oracle (horizon - result.2) result.1)) := by
  rw [Nat.add_comm 1, eval, stored_source_query, PMF.bind_map]
  simp only [Function.comp_def]
  congr 1
  funext answer
  exact storedCallback_law code oracle machine request answer.1 sourceTrace
    ((request, answer.2) :: externalTrace) layout key (decodeCiphertext answer.2) horizon
      ((responseOverhead_le width _).trans hHorizon)

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
