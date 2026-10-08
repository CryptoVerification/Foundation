import Foundation.Examples.OneUseInvocation
import Foundation.Examples.OneUseInitialization

/-! One actual experiment includes native uniform key generation, private
initialization, source call capture, operand preparation, encryption, response
delivery and the caller's actual halt. Width does not change either code. -/
namespace Foundation.OneUseExperimentExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.call, .native .halt]
variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) {width : Nat} (message : Bits width)

def callerMachine : Machine.Configuration :=
  { outputTape := RequestExport.packetTape [] [] message.toList }

def caller : Configuration State := ⟨state, .running (callerMachine message), trace⟩

def operands (key : Bits width) : Machine.PairPreparation.Input :=
  ⟨key.toList, message.toList, [], [], by simp⟩

noncomputable def encryption : Procedure (OneUseSource.step listProcedure.code code oracle) (Bits width) Unit :=
  Procedure.ofFixed _
    (fun key => .source false (Machine.PairPreparation.operand [] key.toList []) (caller state trace message))
    (fun key _ => OneUseInvocationExamples.final (callerMachine message) state trace (operands message key))
    (fun _ => PMF.pure ()) (fun _ => 33 * width + 34)
    (fun key => by
      simpa only [operands, Bits.length_toList, PMF.pure_map, caller] using
        (OneUseInvocationExamples.run code oracle (callerMachine message) state trace (operands message key)
          (by rfl) (by rfl) (by rfl) (by rfl)))

noncomputable def continuation :=
  (encryption oracle state trace message).transport
    (OneUseInitialization.step Machine.OneTimePad.keygen listProcedure.code code oracle (caller state trace message))
    OneUseInitialization.Control.active (fun _ => rfl)

noncomputable def complete :=
  (OneUseInitializationExamples.initialization listProcedure.code code oracle (caller state trace message) width).seq
    ((continuation oracle state trace message).reindex (fun result => result.1))
    (fun _ _ _ => rfl) (fun _ => 33 * width + 34) (fun _ _ _ => Nat.le_refl _)

theorem budget : (complete oracle state trace message).budget () = 39 * width + 39 := by
  change (OneUseInitializationExamples.initialization listProcedure.code code oracle (caller state trace message) width).budget () + (33 * width + 34) = _
  rw [OneUseInitializationExamples.budget]
  omega

def final (key : Bits width) : OneUseInitialization.Control State :=
  .active (OneUseInvocationExamples.final (callerMachine message) state trace (operands message key))

theorem semantics : (complete oracle state trace message).semantics () =
    (uniform (Bits width)).map (fun key => ((key, ()), ())) := by
  simp [complete, continuation, encryption, OneUseInitializationExamples.initialization,
    OneUseInitialization.semantics, Machine.PrivateBitGeneration.native, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.transport, Procedure.ofFixed,
    PMF.map, Function.comp_def]

theorem distribution :
    ((complete oracle state trace message).costed ()).map
      (fun result => (complete oracle state trace message).exit () result.1) =
      (uniform (Bits width)).map (final state trace message) := by
  have h := congrArg (fun distribution => distribution.map ((complete oracle state trace message).exit ()))
    ((complete oracle state trace message).correct ())
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h

theorem run :
    TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen listProcedure.code code oracle (caller state trace message))
      (39 * width + 39)
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).map (final state trace message) := by
  have h := (complete oracle state trace message).final_run ()
    (fun result _ => by
      simp [complete, continuation, encryption, Procedure.seq, Procedure.reindex, Procedure.transport,
        Procedure.ofFixed, OneUseInitialization.step, OneUseSource.step, OneUseInvocationExamples.final,
        Reification.timedStep, Reification.terminal, PMF.pure_map])
    (39 * width + 39) (by rw [budget])
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  change TimedExecution.eval _ _ ((complete oracle state trace message).entry ()) = _
  exact h
/-- Public observation reads the response tape after actual halt.
Private stores and the caller's internal plaintext tape are not exposed. -/
def response : OneUseInitialization.Control State → List Bool
  | .active (.source _ _ frame) => match frame.control with
    | .running machine => machine.outputBits
    | _ => []
  | _ => []

noncomputable def ciphertext :=
  (TimedExecution.eval
    (OneUseInitialization.step Machine.OneTimePad.keygen listProcedure.code code oracle (caller state trace message))
    (39 * width + 39)
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map response

theorem ciphertext_uniform : ciphertext oracle state trace message =
    (uniform (Bits width)).map (fun bits => true :: bits.toList) := by
  unfold ciphertext
  rw [run, PMF.map_comp]
  have he : ∀ key : Bits width, response (final state trace message key) =
      true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList := by
    intro key
    simp [response, final, OneUseInvocationExamples.final, operands, Machine.Configuration.outputBits,
      ResponseLoading.loaded, ResponseLoading.fromCells, Machine.Tape.bits,
      Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor]
    exact (Machine.OneTimePad.toList_xor key message).symm.trans
      ((congrArg Bits.toList (Bits.xor_comm key message)).trans (Machine.OneTimePad.toList_xor message key))
  simp only [Function.comp_def, he]
  have h := congrArg (fun distribution => distribution.map (fun bits : Bits width => true :: bits.toList))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using h

theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace left).bind observer = (ciphertext oracle state trace right).bind observer := by
  rw [ciphertext_uniform, ciphertext_uniform]
end Foundation.OneUseExperimentExamples
