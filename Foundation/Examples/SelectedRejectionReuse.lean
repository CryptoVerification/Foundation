import Foundation.Crypto.Semantics.Oracle.SelectedRejection
import Foundation.Examples.SelectedRejection

/-! Reuse the generic selection/rejection contract for the existing actual
random-bit caller. The descriptor retains its physical call preconditions. -/
namespace Foundation.Examples.SelectedRejectionReuse
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat}
    (native : Machine.Program) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (key : Bits width)
    (rest : List Bool) (tail : List (Option Bool)) (hMismatch : width ≠ rest.length + 1)

def call (bit : Bool) : CryptoOracle.Interactive.SelectedRejection.Call State SourcePrefixExamples.code width where
  machine := SourcePrefixExamples.selectedMachine rest tail bit
  state := state
  trace := trace
  request := bit :: rest
  tail := tail
  active := rfl
  instruction := rfl
  tape := rfl
  mismatch := by simpa only [List.length_cons] using hMismatch

noncomputable def selection :=
  (Foundation.Examples.SelectedRejection.choose native oracle state trace key rest tail).observe
    (call state trace rest tail hMismatch)
    (fun _ result => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨result.state, .running result.machine, result.trace⟩)
    (fun _ _ _ => rfl)

def cap := 2 * (rest.length + 1) + 12 * min width (rest.length + 1) + 29

theorem handoff (start : Unit)
    (chosen : CryptoOracle.Interactive.SelectedRejection.Call State SourcePrefixExamples.code width)
    (_ : chosen ∈ ((selection native oracle state trace key rest tail hMismatch).semantics start).support) :
    (CryptoOracle.Interactive.SelectedRejection.reject native oracle key.toList [] (by simp) chosen).entry () =
      (selection native oracle state trace key rest tail hMismatch).exit start chosen := rfl

theorem bound (start : Unit)
    (chosen : CryptoOracle.Interactive.SelectedRejection.Call State SourcePrefixExamples.code width)
    (h : chosen ∈ ((selection native oracle state trace key rest tail hMismatch).semantics start).support) :
    (CryptoOracle.Interactive.SelectedRejection.reject native oracle key.toList [] (by simp) chosen).budget () ≤
      cap (width := width) rest := by
  change chosen ∈ (sampleBit.map (call state trace rest tail hMismatch)).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨bit, _, he⟩ := h
  subst chosen
  unfold CryptoOracle.Interactive.SelectedRejection.reject
  rw [OneUseSource.rejectedInvocation_budget]
  simp [CryptoOracle.Interactive.SelectedRejection.input, call, Machine.PreparationCheck.consumed, cap]

noncomputable def execution :=
  CryptoOracle.Interactive.SelectedRejection.selected native oracle key.toList [] (by simp)
    (selection native oracle state trace key rest tail hMismatch)
    (handoff native oracle state trace key rest tail hMismatch)
    (fun _ => cap (width := width) rest) (bound native oracle state trace key rest tail hMismatch)

noncomputable def publicRun :=
  ((execution native oracle state trace key rest tail hMismatch).costed ()).map (fun result =>
    (RejectionTiming.publicExit ((execution native oracle state trace key rest tail hMismatch).exit () result.1), result.2))

theorem public_run : publicRun native oracle state trace key rest tail hMismatch =
    CostedComposition.bind
      (sampleBit.map (fun bit => (call state trace rest tail hMismatch bit, 1)))
      (CryptoOracle.Interactive.SelectedRejection.kernel []) := by
  apply CryptoOracle.Interactive.SelectedRejection.selected_public_cost
  simp only [selection, Procedure.observe, Foundation.Examples.SelectedRejection.choose,
    Procedure.ofFixed, PMF.map_comp, Function.comp_def]

theorem key_independence (firstNative secondNative : Machine.Program) (firstKey secondKey : Bits width) :
    publicRun firstNative oracle state trace firstKey rest tail hMismatch =
      publicRun secondNative oracle state trace secondKey rest tail hMismatch := by
  rw [public_run, public_run]

end Foundation.Examples.SelectedRejectionReuse
