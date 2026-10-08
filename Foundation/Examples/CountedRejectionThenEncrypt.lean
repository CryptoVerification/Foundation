import Foundation.Crypto.Semantics.Oracle.CountedRejectionIteration
import Foundation.Examples.CountedCallerNormal

/-! Actual finite counted rejection followed by normal encryption and halt.
The prefix observer retains history but erases the carried plaintext. -/
namespace Foundation.CountedRejectionThenEncryptExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open CountedRejectionIteration
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (past : List (Option Bool))
    (markers : List Bool) (hMismatch : width ≠ 1) (hWidth : width ≠ 0)

def start (message : Bits width) : Value State :=
  ⟨past, markers, message.toList, state, trace⟩

noncomputable def before (message key : Bits width) :=
  (prepare Machine.OneTimePad.Prepared.listProcedure.code oracle key hMismatch
    (start state trace past markers message)).observe
    (fun output => erasePayload output.1)
    (fun _ output => CodeRelocation.oneUse CountedCaller.before.length
      (.source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨output.state, .running (CountedCaller.ready output.past message.toList), output.trace⟩))
    (fun _ output h => by
      rw [prepare_exit]
      rw [prepare_semantics, PMF.mem_support_map_iff] at h
      obtain ⟨value, hValue, he⟩ := h
      subst output
      have hp := payload_preserved Machine.OneTimePad.Prepared.listProcedure.code oracle key hMismatch
        markers.length (start state trace past markers message) value hValue
      change value.payload = message.toList at hp
      simp only [erasePayload]
      rw [hp])

noncomputable def common : PMF (Value State × Nat) :=
  (CostedIteration.eval (kernel hMismatch) markers.length
    (⟨past, markers, [], state, trace⟩ : Value State)).map
      (fun result => (result.1, result.2 + (11 * width + 8)))

theorem before_costed (message key : Bits width) :
    (before oracle state trace past markers hMismatch message key).costed () =
      common state trace past markers hMismatch := by
  change ((prepare Machine.OneTimePad.Prepared.listProcedure.code oracle key hMismatch
    (start state trace past markers message)).costed ()).map _ = _
  rw [prepare_public_cost]
  simp only [start, erasePayload, Bits.length_toList, common]

theorem before_budget (message key : Bits width) :
    (before oracle state trace past markers hMismatch message key).budget () =
      markers.length * (12 * min width 1 + 36) + 11 * width + 8 := by
  change (prepare Machine.OneTimePad.Prepared.listProcedure.code oracle key hMismatch
    (start state trace past markers message)).budget () = _
  rw [prepare_budget]
  simp [start]

theorem before_entry (message key : Bits width) :
    (before oracle state trace past markers hMismatch message key).entry () =
      .source false (Machine.PairPreparation.operand [] key.toList [])
        (frame (start state trace past markers message)) :=
  prepare_entry Machine.OneTimePad.Prepared.listProcedure.code oracle key hMismatch _

def machine (value : Value State) (bits : Bits width) :=
  (CountedCaller.ready value.past bits.toList).rebasePc CountedCaller.before.length

include hWidth in
theorem handoff (message key : Bits width) (input : Unit) (output : Value State)
    (_ : output ∈ ((before oracle state trace past markers hMismatch message key).semantics input).support) :
    (OneUseAdaptiveSecrecyExamples.normal CountedCaller.code oracle Value.state Value.trace
      (fun _ => message) machine
      (fun value bits => CountedCaller.ready_active value.past bits.toList)
      (fun value bits => CountedCaller.ready_call value.past bits.toList)
      (fun value bits => CountedCaller.ready_tape value.past bits.toList
        (CountedCallerNormalExamples.nonempty hWidth bits))
      (fun value bits => CountedCaller.ready_halt value.past bits.toList) key).entry output =
      (before oracle state trace past markers hMismatch message key).exit input output := rfl

noncomputable def ciphertext (message : Bits width) :=
  (uniform (Bits width)).bind (fun key =>
    (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code CountedCaller.code oracle)
      (markers.length * (12 * min width 1 + 36) + 44 * width + 42)
      (.source false (Machine.PairPreparation.operand [] key.toList [])
        (frame (start state trace past markers message)))).map OneUseAdaptiveSecrecyExamples.packet)

include hWidth hMismatch in
theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace past markers left).bind observer =
      (ciphertext oracle state trace past markers right).bind observer := by
  have h := OneUseAdaptiveSecrecyExamples.machine_perfect_secrecy CountedCaller.code oracle
    Value.state Value.trace machine
    (fun value bits => CountedCaller.ready_active value.past bits.toList)
    (fun value bits => CountedCaller.ready_call value.past bits.toList)
    (fun value bits => CountedCaller.ready_tape value.past bits.toList
      (CountedCallerNormalExamples.nonempty hWidth bits))
    (fun value bits => CountedCaller.ready_halt value.past bits.toList)
    (fun _ => left) (fun _ => right)
    (before oracle state trace past markers hMismatch left)
    (before oracle state trace past markers hMismatch right)
    (handoff oracle state trace past markers hMismatch hWidth left)
    (handoff oracle state trace past markers hMismatch hWidth right)
    () (common state trace past markers hMismatch)
    (before_costed oracle state trace past markers hMismatch left)
    (before_costed oracle state trace past markers hMismatch right)
    (markers.length * (12 * min width 1 + 36) + 44 * width + 42)
    (fun key => by rw [before_budget]; omega)
    (fun key => by rw [before_budget]; omega) observer
  simpa only [ciphertext, before_entry] using h

end Foundation.CountedRejectionThenEncryptExamples
