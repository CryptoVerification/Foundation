import Foundation.Examples.RankedVariableTime
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeFixedComponent

/-! Reuse a fixed-horizon proof without mistaking its padded cost for the
actual branch-dependent stopping time. The native code is unchanged. -/
namespace Foundation.Examples.NativeFirstArrival
open Machine Foundation.Probability TimedExecution

noncomputable def padded : NativeComponent Tape Configuration :=
  NativeComponent.ofFixed Foundation.Examples.RankedVariableTime.code Foundation.Examples.RankedVariableTime.initial (fun _ state => state)
    (fun input => (Foundation.Examples.RankedVariableTime.native.execution.semantics input).map Subtype.val) (fun _ => 4)
    (fun input => by
      rw [PMF.map_comp]
      exact Foundation.Examples.RankedVariableTime.native.final_run input (fun output _ => output.property.2) 4 (Nat.le_refl _))
    (by decide) (fun _ => by change 0 < 4; decide) (fun _ => rfl)
    (fun input state hState => by
      rw [PMF.mem_support_map_iff] at hState
      obtain ⟨output, _, rfl⟩ := hState
      exact output.property.2)

theorem same_code : padded.firstArrival.procedure.code = Foundation.Examples.RankedVariableTime.code := rfl

theorem actual_joint (input : Tape) :
    padded.firstArrival.procedure.execution.costed input =
      sampleBit.map (fun bit => (Foundation.Examples.RankedVariableTime.finish input bit, if bit then 4 else 3)) := by
  rw [padded.firstArrival_costed]
  exact Foundation.Examples.RankedVariableTime.boundary_law input

theorem actual_joint_any_horizon (input : Tape) (horizon : Nat) (hTime : 4 ≤ horizon) :
    runToBoundary (stepPMF Foundation.Examples.RankedVariableTime.code) Configuration.halted horizon (Foundation.Examples.RankedVariableTime.initial input) =
      sampleBit.map (fun bit => (Foundation.Examples.RankedVariableTime.finish input bit, if bit then 4 else 3)) := by
  have h := padded.firstArrival_costed_horizon input horizon hTime
  change runToBoundary (stepPMF Foundation.Examples.RankedVariableTime.code) Configuration.halted horizon
    (Foundation.Examples.RankedVariableTime.initial input) = _ at h
  exact h.trans (actual_joint input)

theorem padded_reports_four (input : Tape) (result : Configuration × Nat)
    (hResult : result ∈ (padded.procedure.execution.costed input).support) : result.2 = 4 := by
  change result ∈ (((Foundation.Examples.RankedVariableTime.native.execution.semantics input).map Subtype.val).map
    (fun state => (state, 4))).support at hResult
  rw [PMF.mem_support_map_iff] at hResult
  obtain ⟨state, _, rfl⟩ := hResult
  rfl

end Foundation.Examples.NativeFirstArrival
