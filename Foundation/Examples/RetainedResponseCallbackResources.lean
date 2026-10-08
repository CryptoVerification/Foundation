import Foundation.Examples.RetainedResponseCallback
import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffCallbackEncoded

/-! Whole-code/state bounds instantiated at the concrete acknowledgement
callback's actual entry, for arbitrary private-key and payload lengths. -/
namespace Foundation.Examples.RetainedResponseCallback
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

private theorem retained_cells (key : List Bool) : (retainedKey key).cells = key.length + 2 := by
  cases key <;> simp [retainedKey, PrivateKeyCopy.restored, Tape.cells] <;> omega

variable {State : Type u} (stateSize : State → Nat) (caller : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request key payload : List Bool)

theorem initial_extent :
    Callback.Storage.extent stateSize caller state trace request
      (.processing (.headerWriting (retainedKey key) payload {})) =
      max (ControllerExtent.metadataExtent stateSize caller state trace request) (key.length + payload.length + 3) := by
  change max (ControllerExtent.metadataExtent stateSize caller state trace request)
    ((retainedKey key).cells + payload.length + 1) = _
  rw [retained_cells]
  congr 1
  omega

theorem initial_pc :
    Callback.Encoded.maxPc caller
      (.processing (.headerWriting (retainedKey key) payload {}) : Callback.Encoded.Control State) = caller.pc := by
  simp [Callback.Encoded.maxPc, Callback.Encoded.activePc, PrivacyEncoding.responderPc]

variable (E : FiniteBitEncoding State) (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hState hOracle in
theorem encoded_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (target : Callback.Encoded.Control State)
    (hTarget : target ∈ (TimedExecution.eval (Callback.step native code oracle caller state trace request) elapsed
      (.processing (.headerWriting (retainedKey key) payload {}))).support) :
    ((Callback.Encoded.completeEncoding E).encode
      (PrivateKeyCopy.code, native, code, ComponentResponseEncoding.frame caller state trace request target)).length ≤
      Callback.Encoded.bound native code caller.pc
        (max (ControllerExtent.metadataExtent stateSize caller state trace request) (key.length + payload.length + 3))
        horizon stateIncrement responseCap := by
  have hb := Callback.Encoded.encoded_peak E stateSize hState caller state trace request native code oracle
    stateIncrement responseCap hOracle horizon elapsed hElapsed
    (.processing (.headerWriting (retainedKey key) payload {})) target hTarget
  simpa only [initial_pc, initial_extent] using hb

end Foundation.Examples.RetainedResponseCallback
