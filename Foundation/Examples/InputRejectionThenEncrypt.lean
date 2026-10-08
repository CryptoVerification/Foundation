import Foundation.Crypto.Semantics.Oracle.BalancedCopy
import Foundation.Crypto.Semantics.Oracle.SelectedRejection
import Foundation.Examples.OneUseAdaptiveSecrecy

/-! One fixed code rejects the empty request, reads the real plaintext input
with balanced branches, prepares a valid call, encrypts, and halts. Neither
the plaintext nor its width is embedded in the instruction list. -/
namespace Foundation.InputRejectionThenEncryptExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (message key : Bits width) (hWidth : width ≠ 0)

def initial : Machine.Configuration :=
  { inputTape := RequestExport.packetTape [] [] message.toList }

def ready (bits : Bits width) : Machine.Configuration :=
  { pc := 17, inputTape := RequestExport.packetTape [none] [] bits.toList,
    outputTape := RequestExport.packetTape [] [] bits.toList }

def firstCall : SelectedRejection.Call State BalancedCopy.code width where
  machine := initial message
  state := state
  trace := trace
  request := []
  tail := []
  active := rfl
  instruction := rfl
  tape := rfl
  mismatch := hWidth

noncomputable def rejected :=
  (SelectedRejection.reject Machine.OneTimePad.Prepared.listProcedure.code oracle key.toList [] (by simp)
    (firstCall state trace message hWidth)).observe (fun _ => ())
    (fun _ _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      (NativeCallback.resumed (initial message).advance state trace [] [false]))
    (fun _ output h => (SelectedRejection.reject_exit Machine.OneTimePad.Prepared.listProcedure.code oracle
      key.toList [] (by simp) (firstCall state trace message hWidth) output h).symm)

noncomputable def copy :=
  Procedure.ofFixed (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code BalancedCopy.code oracle)
    (fun _ : Unit => .source false (Machine.PairPreparation.operand [] key.toList [])
      (NativeCallback.resumed (initial message).advance state trace [] [false]))
    (fun _ _ : Unit => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (ready message), ([], [false]) :: trace⟩)
    (fun _ => PMF.pure ()) (fun _ => 11 * width + 5)
    (fun _ => by
      have ht : ([none] : List (Option Bool)).drop width = [] := by
        cases width with
        | zero => exact False.elim (hWidth rfl)
        | succ n => simp
      simpa [ht, initial, ready, NativeCallback.resumed,
        Machine.Configuration.advance, ResponseLoading.loaded, ResponseLoading.fromCells, PMF.pure_map] using
        BalancedCopy.run Machine.OneTimePad.Prepared.listProcedure.code oracle
          (Machine.PairPreparation.operand [] key.toList []) state (([], [false]) :: trace)
          message.toList [] [none] (some false))

noncomputable def preparation :=
  (rejected oracle state trace message key hWidth).seq (copy oracle state trace message key hWidth)
    (fun _ _ _ => rfl) (fun _ => 11 * width + 5) (fun _ _ _ => Nat.le_refl _)

noncomputable def before :=
  (preparation oracle state trace message key hWidth).observe (fun _ => ())
    (fun _ _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (ready message), ([], [false]) :: trace⟩) (fun _ _ _ => rfl)

def reference : Machine.PreparationCheck.FailureInput :=
  ⟨List.replicate width false, [], [], [], by simpa using hWidth⟩

noncomputable def publicPrefix :=
  (RejectionTiming.costs 10 (RejectionTiming.initial (reference hWidth))).map
    (fun result => ((), result.2 + (11 * width + 24)))

theorem rejected_cost : (rejected oracle state trace message key hWidth).costed () =
    (RejectionTiming.costs 10 (RejectionTiming.initial (reference hWidth))).map
      (fun result => ((), result.2 + 19)) := by
  have h := congrArg (fun distribution => distribution.map (fun result => ((), result.2)))
    (SelectedRejection.reject_public_cost Machine.OneTimePad.Prepared.listProcedure.code oracle key.toList []
      (by simp) (firstCall state trace message hWidth))
  simpa only [rejected, Procedure.observe, SelectedRejection.kernel, SelectedRejection.input,
    firstCall, reference, Machine.PreparationCheck.consumed, List.length_nil, List.length_replicate,
    Nat.min_zero, Nat.mul_zero, Nat.zero_add, PMF.map_comp, Function.comp_def] using h

theorem before_cost : (before oracle state trace message key hWidth).costed () = publicPrefix hWidth := by
  have h := congrArg (fun distribution => distribution.map
    (fun result => ((), result.2 + (11 * width + 5)))) (rejected_cost oracle state trace message key hWidth)
  simp only [before, preparation, copy, Procedure.observe, Procedure.seq, Procedure.ofFixed,
    publicPrefix, Function.comp_def,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, PMF.map, PMF.bind_bind, PMF.pure_bind] at h ⊢
  rw [h]
  congr 1
  funext result
  congr 2
  omega

theorem before_budget : (before oracle state trace message key hWidth).budget () = 11 * width + 34 := by
  change (SelectedRejection.reject Machine.OneTimePad.Prepared.listProcedure.code oracle key.toList [] (by simp)
    (firstCall state trace message hWidth)).budget () + (11 * width + 5) = _
  unfold SelectedRejection.reject
  rw [OneUseSource.rejectedInvocation_budget]
  simp [SelectedRejection.input, firstCall, Machine.PreparationCheck.consumed]
  omega

theorem handoff (start : Unit) (value : Unit)
    (_ : value ∈ ((before oracle state trace message key hWidth).semantics start).support) :
    (OneUseAdaptiveSecrecyExamples.normal BalancedCopy.code oracle (fun _ : Unit => state)
      (fun _ => ([], [false]) :: trace) (fun _ => message) (fun _ => ready)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) key).entry value =
      (before oracle state trace message key hWidth).exit start value := rfl

include hWidth in
theorem machine_perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    ((uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code BalancedCopy.code oracle)
        (44 * width + 68) (.source false (Machine.PairPreparation.operand [] key.toList [])
          ⟨state, .running (initial left), trace⟩)).map OneUseAdaptiveSecrecyExamples.packet)).bind observer =
    ((uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code BalancedCopy.code oracle)
        (44 * width + 68) (.source false (Machine.PairPreparation.operand [] key.toList [])
          ⟨state, .running (initial right), trace⟩)).map OneUseAdaptiveSecrecyExamples.packet)).bind observer := by
  apply OneUseAdaptiveSecrecyExamples.machine_perfect_secrecy BalancedCopy.code oracle
    (fun _ : Unit => state) (fun _ => ([], [false]) :: trace) (fun _ => ready)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => left) (fun _ => right)
    (fun key => before oracle state trace left key hWidth) (fun key => before oracle state trace right key hWidth)
    (fun key => handoff oracle state trace left key hWidth)
    (fun key => handoff oracle state trace right key hWidth)
    () (publicPrefix hWidth) (fun key => before_cost oracle state trace left key hWidth)
    (fun key => before_cost oracle state trace right key hWidth) (44 * width + 68)
  · intro key
    rw [before_budget]
    omega
  · intro key
    rw [before_budget]
    omega

end Foundation.InputRejectionThenEncryptExamples
