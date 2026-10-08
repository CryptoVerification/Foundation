import Foundation.Crypto.Semantics.Oracle.OneUseContinuation
import Foundation.Crypto.Semantics.Oracle.OneUseXorResponse

/-! Arbitrary-width encryption begins at the actual caller's call instruction.
The source's physical request tape and private key store supply the operands. -/
namespace CryptoOracle.Interactive.OneUseXorInvocation
open Foundation.Probability TimedExecution CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool))
    (input : Machine.PairPreparation.Input) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second)

noncomputable def invocation :=
  OneUseSource.invocation listProcedure.code code oracle false
    (Machine.PairPreparation.operand [] input.first input.firstTail) machine state trace input.second
    [] input.secondTail hActive hCall hTape
    (OneUseXorResponse.response code oracle machine.advance state trace input.second input)
    (by
      simp only [hTape, OneUseXorResponse.response, OneUseSource.preparedResponse,
        OneUseSource.preparationPrefix, OneUseSource.preparation, Procedure.seq, Procedure.reindex,
        Procedure.remember, Procedure.liftBoundary, Procedure.ofFixed, Machine.PairPreparation.procedure,
        OneUseSource.embedPreparation, Function.comp_def]
      rfl)

theorem budget : (invocation code oracle machine state trace input hActive hCall hTape).budget () =
    33 * input.first.length + 33 := by
  unfold invocation
  rw [OneUseSource.invocation_budget, OneUseXorResponse.budget]
  have h := input.sameLength
  omega

theorem distribution :
    ((invocation code oracle machine state trace input hActive hCall hTape).costed ()).map
      (fun result => (invocation code oracle machine state trace input hActive hCall hTape).exit () result.1) =
      PMF.pure (OneUseSource.Control.source true
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (NativeCallback.resumed machine.advance state trace input.second
          (true :: Machine.OneTimePad.xorList input.first input.second))) := by
  unfold invocation
  rw [OneUseSource.invocation_distribution, OneUseXorResponse.distribution]
theorem adaptive_resume (horizon : Nat) (hBudget : 33 * input.first.length + 33 ≤ horizon) :
    TimedExecution.eval (OneUseSource.step listProcedure.code code oracle) horizon
      (.source false (Machine.PairPreparation.operand [] input.first input.firstTail)
        ⟨state, .running machine, trace⟩) =
      ((invocation code oracle machine state trace input hActive hCall hTape).costed ()).bind
        (fun result =>
          (TimedExecution.eval (SpentSource.step code oracle) (horizon - result.2)
            (.source (NativeCallback.resumed machine.advance state trace input.second result.1.2.2.2.2.1))).map
              (SpentSource.embed (Machine.PairPreparation.operand [] input.first input.firstTail))) := by
  apply OneUseSource.adaptive_resume_law listProcedure.code code oracle
    (Machine.PairPreparation.operand [] input.first input.firstTail)
    machine state trace input.second [] input.secondTail hActive hCall hTape
    (OneUseXorResponse.response code oracle machine.advance state trace input.second input)
    (by
      simp only [hTape, OneUseXorResponse.response, OneUseSource.preparedResponse,
        OneUseSource.preparationPrefix, OneUseSource.preparation, Procedure.seq, Procedure.reindex,
        Procedure.remember, Procedure.liftBoundary, Procedure.ofFixed, Machine.PairPreparation.procedure,
        OneUseSource.embedPreparation, Function.comp_def]
      rfl)
    (fun output => output.2.2.2.1)
    (fun output hOutput => by
      rw [OneUseXorResponse.semantics, PMF.mem_support_pure_iff] at hOutput
      subst output
      rfl) horizon
  rw [OneUseXorResponse.budget]
  have h := input.sameLength
  omega

def final : OneUseSource.Control State :=
  .source true (Machine.PairPreparation.operand [] input.first input.firstTail)
    ⟨state, .running { machine.advance with
      outputTape := ResponseLoading.loaded (true :: Machine.OneTimePad.xorList input.first input.second), halted := true },
      (input.second, true :: Machine.OneTimePad.xorList input.first input.second) :: trace⟩

variable (hNext : code[machine.advance.pc]? = some (.native .halt))

noncomputable def stop : Procedure (OneUseSource.step listProcedure.code code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .source true (Machine.PairPreparation.operand [] input.first input.firstTail)
      (NativeCallback.resumed machine.advance state trace input.second
        (true :: Machine.OneTimePad.xorList input.first input.second)))
    (fun _ _ => final machine state trace input) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      have hNextPC : code[machine.pc + 1]? = some (.native .halt) := by simpa [Machine.Configuration.advance] using hNext
      simp [TimedExecution.eval, OneUseSource.step, NativeCallback.resumed, hNextPC,
        Machine.Configuration.advance, hActive, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, Machine.Instruction.next, final, PMF.pure_map])

noncomputable def complete :=
  (invocation code oracle machine state trace input hActive hCall hTape).seq
    ((stop code oracle machine state trace input hActive hNext).reindex (fun _ => ()))
    (fun _ result hResult => by
      unfold invocation at hResult
      rw [OneUseSource.invocation_semantics, OneUseXorResponse.semantics,
        PMF.pure_map, PMF.mem_support_pure_iff] at hResult
      subst result
      rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem complete_budget :
    (complete code oracle machine state trace input hActive hCall hTape hNext).budget () =
      33 * input.first.length + 34 := by
  change (invocation code oracle machine state trace input hActive hCall hTape).budget () + 1 = _
  rw [budget]

include hActive hCall hTape hNext in
theorem run :
    TimedExecution.eval (OneUseSource.step listProcedure.code code oracle)
      (33 * input.first.length + 34)
      (.source false (Machine.PairPreparation.operand [] input.first input.firstTail) ⟨state, .running machine, trace⟩) =
      PMF.pure (final machine state trace input) := by
  have h := (complete code oracle machine state trace input hActive hCall hTape hNext).final_run ()
    (fun _ _ => by simp [complete, stop, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
      OneUseSource.step, Reification.timedStep, Reification.terminal, final, PMF.pure_map])
    (33 * input.first.length + 34) (by rw [complete_budget])
  simp only [complete, Procedure.seq] at h
  unfold invocation at h
  rw [OneUseSource.invocation_semantics, OneUseXorResponse.semantics, PMF.pure_map] at h
  simpa only [stop, Procedure.seq, Procedure.ofFixed, Procedure.reindex, PMF.pure_map, PMF.pure_bind, Function.comp_def,
    OneUseSource.invocation, OneUseSource.capture] using h
end CryptoOracle.Interactive.OneUseXorInvocation
