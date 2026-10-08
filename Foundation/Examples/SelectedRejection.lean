import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureIteration
import Foundation.Crypto.Semantics.Oracle.RejectionTiming
import Foundation.Examples.SourcePrefix
import Foundation.Constructions.Symmetric.OneTimePad

/-! Real probabilistic request selection composes with physical rejection.
The key width and request width are arbitrary and unequal; native code is
unrestricted. Runtime resumes the same caller after returning the failure. -/
namespace Foundation.Examples.SelectedRejection
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

abbrev RejectionOutput := Unit × ((Unit × Unit) × (List Bool × Unit))
variable {State : Type u} {width : Nat} (native : Machine.Program) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (key : Bits width)
    (rest : List Bool) (tail : List (Option Bool)) (hMismatch : width ≠ rest.length + 1)

def input (bit : Bool) : Machine.PreparationCheck.FailureInput :=
  ⟨key.toList, bit :: rest, [], tail, by simpa [Nat.add_comm] using hMismatch⟩

noncomputable def choose : Procedure (OneUseSource.step native SourcePrefixExamples.code oracle) Unit Bool :=
  Procedure.ofFixed _
    (fun _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (SourcePrefixExamples.initialMachine rest tail), trace⟩)
    (fun _ bit => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (SourcePrefixExamples.selectedMachine rest tail bit), trace⟩)
    (fun _ => sampleBit) (fun _ => 1) (fun _ => by
      simp only [TimedExecution.eval, OneUseSource.step, PMF.bind_pure]
      change (Reification.timedStep SourcePrefixExamples.code oracle
        ⟨state, .running (SourcePrefixExamples.initialMachine rest tail), trace⟩).map _ = _
      have h := SourcePrefixExamples.choose_run oracle state trace rest tail
      change Reification.timedStep SourcePrefixExamples.code oracle
        ⟨state, .running (SourcePrefixExamples.initialMachine rest tail), trace⟩ = _ at h
      rw [h, PMF.map_comp]
      rfl)

theorem selected_active (bit : Bool) : (SourcePrefixExamples.selectedMachine rest tail bit).halted = false := rfl
theorem selected_call (bit : Bool) : SourcePrefixExamples.code[(SourcePrefixExamples.selectedMachine rest tail bit).pc]? = some .call := rfl
theorem selected_tape (bit : Bool) : (SourcePrefixExamples.selectedMachine rest tail bit).outputTape =
    RequestExport.packetTape [] (input key rest tail hMismatch bit).secondTail (input key rest tail hMismatch bit).second := rfl

noncomputable def reject (bit : Bool) : Procedure (OneUseSource.step native SourcePrefixExamples.code oracle) Unit RejectionOutput :=
  OneUseSource.rejectedInvocation native SourcePrefixExamples.code oracle
    (SourcePrefixExamples.selectedMachine rest tail bit) state trace
    (selected_active rest tail bit) (selected_call rest tail bit)
    (input key rest tail hMismatch bit) (selected_tape key rest tail hMismatch bit)

noncomputable def round :=
  (choose native oracle state trace key rest tail).seq
    (Procedure.dispatch (reject native oracle state trace key rest tail hMismatch))
    (fun _ _ _ => rfl)
    (fun _ => 2 * (rest.length + 1) + 12 * min width (rest.length + 1) + 29)
    (fun _ bit _ => by
      unfold Procedure.dispatch reject
      rw [OneUseSource.rejectedInvocation_budget]
      simp [input, Machine.PreparationCheck.consumed])

theorem budget : (round native oracle state trace key rest tail hMismatch).budget () =
    2 * (rest.length + 1) + 12 * min width (rest.length + 1) + 30 := by
  change 1 + (2 * (rest.length + 1) + 12 * min width (rest.length + 1) + 29) = _
  omega

noncomputable def publicRound :=
  ((round native oracle state trace key rest tail hMismatch).costed ()).map (fun result =>
    (RejectionTiming.publicExit ((round native oracle state trace key rest tail hMismatch).exit () result.1), result.2))

theorem public_round : publicRound native oracle state trace key rest tail hMismatch =
    sampleBit.bind (fun bit =>
      (RejectionTiming.costs (12 * Machine.PreparationCheck.consumed (input key rest tail hMismatch bit) + 10)
        (RejectionTiming.initial (input key rest tail hMismatch bit))).map
          (fun result => (some (NativeCallback.resumed (SourcePrefixExamples.selectedMachine rest tail bit).advance
            state trace (bit :: rest) [false]), 2 * (rest.length + 1) + result.2 + 20))) := by
  simp only [publicRound, round, choose, Procedure.seq, Procedure.dispatch, Procedure.ofFixed,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  congr 1
  funext bit
  have h := congrArg (fun distribution => distribution.map (fun result => (result.1, 1 + result.2)))
    (RejectionTiming.rejected_invocation_costs native SourcePrefixExamples.code oracle
      (SourcePrefixExamples.selectedMachine rest tail bit) state trace (selected_active rest tail bit)
      (selected_call rest tail bit) (input key rest tail hMismatch bit) (selected_tape key rest tail hMismatch bit))
  simp only [reject, PMF.map_comp, Function.comp_def, input, List.length_cons,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h ⊢
  rw [h]
  congr 1
  funext result
  congr 1
  omega

theorem key_independence (firstNative secondNative : Machine.Program) (firstKey secondKey : Bits width) :
    publicRound firstNative oracle state trace firstKey rest tail hMismatch =
      publicRound secondNative oracle state trace secondKey rest tail hMismatch := by
  rw [public_round, public_round]
  congr 1
  funext bit
  have hp := RejectionTiming.preparation_cost_independence firstNative secondNative
    SourcePrefixExamples.code SourcePrefixExamples.code oracle oracle
    (SourcePrefixExamples.selectedMachine rest tail bit).advance (SourcePrefixExamples.selectedMachine rest tail bit).advance
    state state trace trace (bit :: rest) (bit :: rest)
    (input firstKey rest tail hMismatch bit) (input secondKey rest tail hMismatch bit)
    (by simp [input]) rfl rfl rfl
  change RejectionTiming.costs
      (12 * Machine.PreparationCheck.consumed (input firstKey rest tail hMismatch bit) + 10)
      (RejectionTiming.initial (input firstKey rest tail hMismatch bit)) =
    RejectionTiming.costs
      (12 * Machine.PreparationCheck.consumed (input secondKey rest tail hMismatch bit) + 10)
      (RejectionTiming.initial (input secondKey rest tail hMismatch bit)) at hp
  rw [hp]

end Foundation.Examples.SelectedRejection
