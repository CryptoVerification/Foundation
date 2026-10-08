import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyMachine
import Foundation.Constructions.Symmetric.EncryptThenMAC.AuthenticateResponseLayout

/-! Connect the actual native authentication output layouts to the concrete
privacy controller's cell-level response return. The two stopping layouts
have different costs; no artificial tape reset or caller padding is used. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def returnBudget (width : Nat) : Option Bool → Nat
  | none => 5
  | some _ => 3 * width + 9

theorem return_authentication_run {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (storedKey : Tape) (key : TableMAC.Key width)
    (ciphertext : Option Bool) (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (returnBudget width ciphertext)
      ⟨state, .rewinding storedKey machine request (AuthenticateResponse.responseTape key ciphertext), sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source storedKey (.loading machine
        (AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) {}),
        (request, AuthenticateResponse.encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit)))) :: sourceTrace,
        externalTrace⟩ := by
  cases ciphertext with
  | none => exact return_single_response_run code oracle storedKey machine request false state sourceTrace externalTrace
  | some bit =>
      simpa [returnBudget, AuthenticateResponse.responseTape, AuthenticateResponse.encode, Nat.mul_add, Nat.add_assoc] using
        return_response_run code oracle storedKey machine request
          ([true, bit] ++ (TableMAC.sign key bit).toList) state sourceTrace externalTrace

/-- The explicit native output layout agrees with the response function
used in the existing semantic privacy reduction. -/
theorem return_privacy_response {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (storedKey : Tape) (key : TableMAC.Key width)
    (ciphertext : Option Bool) (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (returnBudget width ciphertext)
      ⟨state, .rewinding storedKey machine request (AuthenticateResponse.responseTape key ciphertext), sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source storedKey (.loading machine
        (AuthenticateResponse.encode (authenticate OneBitEncryption.scheme
          (TableMAC.scheme (fun _ => width)) 0 key ciphertext)) {}),
        (request, AuthenticateResponse.encode (authenticate OneBitEncryption.scheme
          (TableMAC.scheme (fun _ => width)) 0 key ciphertext)) :: sourceTrace, externalTrace⟩ :=
  return_authentication_run code oracle storedKey key ciphertext machine request state sourceTrace externalTrace

/-- The response controller produces the exact tape consumed by the privacy
machine's completion test, jointly with its retained physical key store. -/
theorem completed_response_layout {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval ((ResponseHandoff.keyBytes key).length +
      (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14))
      (ResponseHandoff.copied key ciphertext)).map responseOutput =
      PMF.pure (some (ResponseHandoff.retainedKey key, AuthenticateResponse.responseTape key ciphertext)) := by
  rw [ResponseHandoff.eval_add, ResponseHandoff.copied_to_authentication, PMF.pure_bind,
    ResponseHandoff.authenticate_eval, PMF.map_comp]
  have hInput : (ResponseHandoff.preparedMachine key ciphertext).inputTape.Equivalent
      (Tape.ofBits (AuthenticateResponse.input key ciphertext)) := by
    cases ciphertext with
    | none => simpa [ResponseHandoff.preparedMachine, AuthenticateResponse.input, ResponseHandoff.header,
        ResponseHandoff.keyBytes] using ResponseHandoff.prepared_equivalent ([false] ++ ResponseHandoff.keyBytes key)
    | some bit => simpa [ResponseHandoff.preparedMachine, AuthenticateResponse.input, ResponseHandoff.header,
        ResponseHandoff.keyBytes] using ResponseHandoff.prepared_equivalent ([true, bit] ++ ResponseHandoff.keyBytes key)
  have hLayout := AuthenticateResponse.output_layout_of_equivalent key ciphertext _ hInput
  have h := congrArg (fun distribution => distribution.map
    (fun pair : Bool × Tape => if pair.1 then some (ResponseHandoff.retainedKey key, pair.2) else none)) hLayout
  simpa only [PMF.map_comp, PMF.pure_map, Function.comp_def, responseOutput,
    ResponseHandoff.preparedMachine, ↓reduceIte] using h

/-- Lift an actual completed native copy into the complete response job.
The copy's real trace may end before its bound; only the halted response
frame absorbs the remaining budget, not a running source machine. -/
theorem completed_response_of_copy_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool)
    (copyStart : Configuration)
    (hCopyRun : evalConfigWithin PrivateKeyCopy.code copyStart (8 * (ResponseHandoff.keyBytes key).length + 5) =
      PMF.pure (PrivateKeyCopy.finish (ResponseHandoff.keyBytes key)
        ((ResponseHandoff.header ciphertext).reverse.map some))) :
    (ResponseHandoff.eval ((8 * (ResponseHandoff.keyBytes key).length + 5) +
      ((ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14)))
      (.copying copyStart)).map responseOutput =
      PMF.pure (some (ResponseHandoff.retainedKey key, AuthenticateResponse.responseTape key ciphertext)) := by
  let copyBudget := 8 * (ResponseHandoff.keyBytes key).length + 5
  let responseBudget := (ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14)
  have hm : PrivateKeyCopy.finish (ResponseHandoff.keyBytes key)
      ((ResponseHandoff.header ciphertext).reverse.map some) ∈
      (evalConfigWithin PrivateKeyCopy.code copyStart copyBudget).support := by
    rw [hCopyRun, PMF.mem_support_pure_iff]
  have hPadded := (mem_support_evalConfigWithin_iff _ _ _ _).mp hm
  obtain ⟨used, hUsed, actual⟩ := hPadded.toRunsFor_le
  have hActual := ResponseHandoff.copying_runs actual
  have hBudget : copyBudget + responseBudget = used + (responseBudget + (copyBudget - used)) := by omega
  change (ResponseHandoff.eval (copyBudget + responseBudget) (.copying copyStart)).map _ = _
  rw [hBudget, ResponseHandoff.eval_add, hActual, PMF.pure_bind]
  change (ResponseHandoff.eval (responseBudget + (copyBudget - used)) (ResponseHandoff.copied key ciphertext)).map _ = _
  rw [ResponseHandoff.eval_stable _ responseBudget (copyBudget - used) (ResponseHandoff.response_stops key ciphertext)]
  exact completed_response_layout key ciphertext

/-- Full physical-output law starting from the native-generated private
store, including header writing and actual copy execution. -/
theorem generated_completed_response {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval (ResponseHandoff.budget width ciphertext)
      (GeneratedResponse.initial key ciphertext)).map responseOutput =
      PMF.pure (some (ResponseHandoff.retainedKey key, AuthenticateResponse.responseTape key ciphertext)) := by
  have hBudget : ResponseHandoff.budget width ciphertext =
      (2 * (ResponseHandoff.header ciphertext).length + 1) +
        ((8 * (ResponseHandoff.keyBytes key).length + 5) +
          ((ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14))) := by
    rw [ResponseHandoff.keyBytes_length]
    unfold ResponseHandoff.budget
    omega
  rw [hBudget, ResponseHandoff.eval_add]
  unfold GeneratedResponse.initial
  rw [ResponseHandoff.header_eval, PMF.pure_bind]
  simp only [List.append_nil]
  change (ResponseHandoff.eval _ (.copying
    (GeneratedResponse.copying [] (ResponseHandoff.keyBytes key) ((ResponseHandoff.header ciphertext).reverse.map some)))).map _ = _
  exact completed_response_of_copy_run key ciphertext _ (GeneratedResponse.copy_run _ _)

/-- Sum of the proved response-stage budgets, including the transition
which transfers the authenticated native output to the return controller.
This is not yet a bound for an arbitrary complete source attack. -/
def responseOverhead (width : Nat) (ciphertext : Option Bool) : Nat :=
  ResponseHandoff.budget width ciphertext + 1 + returnBudget width ciphertext

theorem responseOverhead_le (width : Nat) (ciphertext : Option Bool) :
    responseOverhead width ciphertext ≤ 29 * width + 38 := by
  cases ciphertext <;> simp [responseOverhead, ResponseHandoff.budget, ResponseHandoff.header, returnBudget] <;> omega

theorem response_profile_polynomial {width : Nat → Nat} (h : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 29 * width n + 38) :=
  ((PolynomiallyBounded.const 29).mul h).add (PolynomiallyBounded.const 38)

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
