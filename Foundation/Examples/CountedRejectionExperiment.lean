import Foundation.Examples.CountedRejectionThenEncrypt
import Foundation.Examples.OneUseInitialization
import Foundation.Crypto.Semantics.Oracle.InitializationContinuation

/-! Actual native key generation, arbitrary finite counted rejections,
input reading, normal encryption, and halt, all in one transition system. -/
namespace Foundation.CountedRejectionExperimentExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open CountedRejectionIteration
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (past : List (Option Bool))
    (markers : List Bool) (message : Bits width) (hMismatch : width ≠ 1) (hWidth : width ≠ 0)

def caller : Configuration State :=
  frame (CountedRejectionThenEncryptExamples.start state trace past markers message)

noncomputable def suffix : Procedure
    (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code CountedCaller.code oracle)
    (Bits width) (Value State × Unit) :=
  Procedure.dispatch (fun key : Bits width =>
    OneUseAdaptiveSecrecyExamples.complete CountedCaller.code oracle Value.state Value.trace
      (fun _ => message) CountedRejectionThenEncryptExamples.machine
      (fun value bits => CountedCaller.ready_active value.past bits.toList)
      (fun value bits => CountedCaller.ready_call value.past bits.toList)
      (fun value bits => CountedCaller.ready_tape value.past bits.toList
        (CountedCallerNormalExamples.nonempty hWidth bits))
      (fun value bits => CountedCaller.ready_halt value.past bits.toList)
      (CountedRejectionThenEncryptExamples.before oracle state trace past markers hMismatch message)
      (CountedRejectionThenEncryptExamples.handoff oracle state trace past markers hMismatch hWidth message) key)

theorem suffix_entry (key : Bits width) :
    (suffix oracle state trace past markers message hMismatch hWidth).entry key =
      .source false (Machine.PairPreparation.operand [] key.toList []) (caller state trace past markers message) :=
  CountedRejectionThenEncryptExamples.before_entry oracle state trace past markers hMismatch message key

theorem suffix_budget (key : Bits width) :
    (suffix oracle state trace past markers message hMismatch hWidth).budget key =
      markers.length * (12 * min width 1 + 36) + 44 * width + 42 := by
  change (CountedRejectionThenEncryptExamples.before oracle state trace past markers hMismatch message key).budget () +
    (33 * width + 34) = _
  rw [CountedRejectionThenEncryptExamples.before_budget]
  omega

noncomputable def whole :=
  OneUseInitialization.follow Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
    CountedCaller.code oracle (caller state trace past markers message)
    (OneUseInitializationExamples.initialization Machine.OneTimePad.Prepared.listProcedure.code
      CountedCaller.code oracle (caller state trace past markers message) width)
    (fun key : Bits width => Machine.PairPreparation.operand [] key.toList []) (fun _ _ _ => rfl)
    (suffix oracle state trace past markers message hMismatch hWidth)
    (suffix_entry oracle state trace past markers message hMismatch hWidth)
    (fun _ => markers.length * (12 * min width 1 + 36) + 44 * width + 42)
    (fun _ result _ => le_of_eq (suffix_budget oracle state trace past markers message hMismatch hWidth result.1))

theorem budget : (whole oracle state trace past markers message hMismatch hWidth).budget () =
    markers.length * (12 * min width 1 + 36) + 50 * width + 47 := by
  unfold whole
  rw [OneUseInitialization.follow_budget, OneUseInitializationExamples.budget]
  omega

def response : OneUseInitialization.Control State → List Bool
  | .active source => OneUseAdaptiveSecrecyExamples.packet source
  | _ => []

theorem suffix_response (key : Bits width) (result : Value State × Unit) :
    response (.active ((suffix oracle state trace past markers message hMismatch hWidth).exit key result)) =
      true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList := by
  rcases result with ⟨value, result⟩
  cases result
  simp [response, suffix, Procedure.dispatch, OneUseAdaptiveSecrecyExamples.complete,
    Procedure.seq, OneUseAdaptiveSecrecyExamples.normal, Procedure.ofFixed,
    OneUseInvocationExamples.final, OneUseAdaptiveSecrecyExamples.packet,
    OneUseAdaptiveSecrecyExamples.operands, Machine.Configuration.outputBits,
    ResponseLoading.loaded, ResponseLoading.fromCells, Machine.Tape.bits,
    Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor]
  exact (Machine.OneTimePad.toList_xor key message).symm.trans
    ((congrArg Bits.toList (Bits.xor_comm key message)).trans (Machine.OneTimePad.toList_xor message key))

noncomputable def ciphertext :=
  (TimedExecution.eval
    (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
      CountedCaller.code oracle (caller state trace past markers message))
    (markers.length * (12 * min width 1 + 36) + 50 * width + 47)
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map response

include hMismatch hWidth in
theorem ciphertext_uniform : ciphertext oracle state trace past markers message =
    (uniform (Bits width)).map (fun bits => true :: bits.toList) := by
  have h := (whole oracle state trace past markers message hMismatch hWidth).final_run ()
    (fun _ _ => by
      simp [whole, OneUseInitialization.follow, Procedure.seq, Procedure.reindex, Procedure.transport,
        suffix, Procedure.dispatch, OneUseAdaptiveSecrecyExamples.complete, OneUseAdaptiveSecrecyExamples.normal,
        Procedure.ofFixed, OneUseInvocationExamples.final, OneUseInitialization.step, OneUseSource.step,
        Reification.timedStep, Reification.terminal, PMF.pure_map])
    (markers.length * (12 * min width 1 + 36) + 50 * width + 47) (by rw [budget])
  have hr := congrArg (fun dist => dist.map response) h
  change ciphertext oracle state trace past markers message = _ at hr
  rw [PMF.map_comp] at hr
  rw [hr]
  change ((whole oracle state trace past markers message hMismatch hWidth).semantics ()).map
    (fun result => response (.active ((suffix oracle state trace past markers message hMismatch hWidth).exit result.1.1 result.2))) = _
  simp only [suffix_response]
  unfold whole
  rw [OneUseInitialization.follow_semantics]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((OneUseInitializationExamples.initialization Machine.OneTimePad.Prepared.listProcedure.code
    CountedCaller.code oracle (caller state trace past markers message) width).semantics ()).bind
      (fun first => ((suffix oracle state trace past markers message hMismatch hWidth).semantics first.1).map
        (Function.const _ (true :: (Foundation.Symmetric.OneTimePad.encrypt first.1 message).toList))) = _
  simp only [PMF.map_const]
  change ((OneUseInitializationExamples.initialization Machine.OneTimePad.Prepared.listProcedure.code
    CountedCaller.code oracle (caller state trace past markers message) width).semantics ()).map
      (fun first => true :: (Foundation.Symmetric.OneTimePad.encrypt first.1 message).toList) = _
  have hk := congrArg (fun dist => dist.map
    (fun key => true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList))
    (OneUseInitializationExamples.key_distribution Machine.OneTimePad.Prepared.listProcedure.code
      CountedCaller.code oracle (caller state trace past markers message) width)
  rw [PMF.map_comp] at hk
  change ((OneUseInitializationExamples.initialization Machine.OneTimePad.Prepared.listProcedure.code
    CountedCaller.code oracle (caller state trace past markers message) width).semantics ()).map
      (fun first => true :: (Foundation.Symmetric.OneTimePad.encrypt first.1 message).toList) = _ at hk
  rw [hk]
  have hu := congrArg (fun dist => dist.map (fun bits : Bits width => true :: bits.toList))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using hu

include hMismatch hWidth in
theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace past markers left).bind observer =
      (ciphertext oracle state trace past markers right).bind observer := by
  rw [ciphertext_uniform oracle state trace past markers left hMismatch hWidth,
    ciphertext_uniform oracle state trace past markers right hMismatch hWidth]

end Foundation.CountedRejectionExperimentExamples
