import Foundation.Examples.InputRejectionThenEncrypt
import Foundation.Examples.OneUseInitialization
import Foundation.Crypto.Semantics.Oracle.InitializationContinuation

/-! Native key generation, transfer of the physical private tape, rejection,
fixed-code plaintext reading, normal encryption, response and actual halt.
All code is independent of both the width and plaintext value. -/
namespace Foundation.InputRejectionExperimentExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (message : Bits width) (hWidth : width ≠ 0)

def caller : Configuration State := ⟨state, .running (InputRejectionThenEncryptExamples.initial message), trace⟩

noncomputable def suffix :=
  Procedure.dispatch (fun key : Bits width =>
    OneUseAdaptiveSecrecyExamples.complete BalancedCopy.code oracle
      (fun _ : Unit => state) (fun _ => ([], [false]) :: trace) (fun _ => message)
      (fun _ => InputRejectionThenEncryptExamples.ready)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun key => InputRejectionThenEncryptExamples.before oracle state trace message key hWidth)
      (fun key => InputRejectionThenEncryptExamples.handoff oracle state trace message key hWidth) key)

theorem suffix_budget (key : Bits width) : (suffix oracle state trace message hWidth).budget key = 44 * width + 68 := by
  change (InputRejectionThenEncryptExamples.before oracle state trace message key hWidth).budget () +
    (33 * width + 34) = _
  rw [InputRejectionThenEncryptExamples.before_budget]
  omega

theorem before_semantics (key : Bits width) :
    (InputRejectionThenEncryptExamples.before oracle state trace message key hWidth).semantics () = PMF.pure () := by
  have h := (InputRejectionThenEncryptExamples.before oracle state trace message key hWidth).correct ()
  rw [InputRejectionThenEncryptExamples.before_cost] at h
  unfold InputRejectionThenEncryptExamples.publicPrefix at h
  rw [PMF.map_comp] at h
  change (RejectionTiming.costs 10 (RejectionTiming.initial (InputRejectionThenEncryptExamples.reference hWidth))).map
    (Function.const _ ()) = _ at h
  rw [PMF.map_const] at h
  exact h.symm

theorem suffix_semantics (key : Bits width) :
    (suffix oracle state trace message hWidth).semantics key = PMF.pure ((), ()) := by
  simp [suffix, Procedure.dispatch, OneUseAdaptiveSecrecyExamples.complete, Procedure.seq,
    before_semantics oracle state trace message hWidth key, OneUseAdaptiveSecrecyExamples.normal,
    Procedure.ofFixed, PMF.pure_map]

noncomputable def whole :=
  OneUseInitialization.follow Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
    BalancedCopy.code oracle (caller state trace message)
    (OneUseInitializationExamples.initialization Machine.OneTimePad.Prepared.listProcedure.code
      BalancedCopy.code oracle (caller state trace message) width)
    (fun key : Bits width => Machine.PairPreparation.operand [] key.toList []) (fun _ _ _ => rfl)
    (suffix oracle state trace message hWidth) (fun _ => rfl)
    (fun _ => 44 * width + 68)
    (fun _ result _ => le_of_eq (suffix_budget oracle state trace message hWidth result.1))

theorem budget : (whole oracle state trace message hWidth).budget () = 50 * width + 73 := by
  unfold whole
  rw [OneUseInitialization.follow_budget, OneUseInitializationExamples.budget]
  omega

theorem semantics : (whole oracle state trace message hWidth).semantics () =
    (uniform (Bits width)).map (fun key => ((key, ()), ((), ()))) := by
  unfold whole
  rw [OneUseInitialization.follow_semantics]
  simp only [OneUseInitializationExamples.initialization, OneUseInitialization.semantics,
    Machine.PrivateBitGeneration.native, Machine.Procedure.ofFixed, Procedure.ofFixed,
    PMF.bind_map, Function.comp_def]
  simp only [suffix_semantics, PMF.pure_map, PMF.bind_pure_comp]
  rfl

noncomputable def final (key : Bits width) : OneUseInitialization.Control State :=
  .active ((suffix oracle state trace message hWidth).exit key ((), ()))

theorem distribution : ((whole oracle state trace message hWidth).costed ()).map
    (fun result => (whole oracle state trace message hWidth).exit () result.1) =
      (uniform (Bits width)).map (final oracle state trace message hWidth) := by
  have h := congrArg (fun distribution => distribution.map ((whole oracle state trace message hWidth).exit ()))
    ((whole oracle state trace message hWidth).correct ())
  rw [semantics, PMF.map_comp] at h
  have he : ∀ key, (whole oracle state trace message hWidth).exit () ((key, ()), ((), ())) =
      final oracle state trace message hWidth key := by intro key; rfl
  simpa only [PMF.map_comp, Function.comp_def, he] using h

include hWidth in
theorem run :
    TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
        BalancedCopy.code oracle (caller state trace message))
      (50 * width + 73) (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).map (final oracle state trace message hWidth) := by
  have h := (whole oracle state trace message hWidth).final_run ()
    (fun _ _ => by
      simp [whole, OneUseInitialization.follow, Procedure.seq, Procedure.reindex, Procedure.transport,
        suffix, Procedure.dispatch, OneUseAdaptiveSecrecyExamples.complete, OneUseAdaptiveSecrecyExamples.normal,
        Procedure.ofFixed, OneUseInvocationExamples.final, OneUseInitialization.step, OneUseSource.step,
        Reification.timedStep, Reification.terminal, PMF.pure_map])
    (50 * width + 73) (by rw [budget])
  rw [semantics, PMF.map_comp] at h
  exact h

def response : OneUseInitialization.Control State → List Bool
  | .active source => OneUseAdaptiveSecrecyExamples.packet source
  | _ => []

noncomputable def ciphertext :=
  (TimedExecution.eval
    (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
      BalancedCopy.code oracle (caller state trace message))
    (50 * width + 73) (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map response

include hWidth in
theorem ciphertext_uniform : ciphertext oracle state trace message =
    (uniform (Bits width)).map (fun bits => true :: bits.toList) := by
  unfold ciphertext
  rw [run oracle state trace message hWidth, PMF.map_comp]
  have he : ∀ key : Bits width, response (final oracle state trace message hWidth key) =
      true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList := by
    intro key
    simp [response, final, suffix, Procedure.dispatch, OneUseAdaptiveSecrecyExamples.complete,
      OneUseAdaptiveSecrecyExamples.normal, Procedure.seq, Procedure.ofFixed,
      OneUseInvocationExamples.final, OneUseAdaptiveSecrecyExamples.packet,
      OneUseAdaptiveSecrecyExamples.operands, Machine.Configuration.outputBits,
      ResponseLoading.loaded, ResponseLoading.fromCells, Machine.Tape.bits,
      Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor]
    exact (Machine.OneTimePad.toList_xor key message).symm.trans
      ((congrArg Bits.toList (Bits.xor_comm key message)).trans (Machine.OneTimePad.toList_xor message key))
  simp only [Function.comp_def, he]
  have h := congrArg (fun distribution => distribution.map (fun bits : Bits width => true :: bits.toList))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using h

include hWidth in
theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace left).bind observer = (ciphertext oracle state trace right).bind observer := by
  rw [ciphertext_uniform oracle state trace left hWidth, ciphertext_uniform oracle state trace right hWidth]

end Foundation.InputRejectionExperimentExamples
