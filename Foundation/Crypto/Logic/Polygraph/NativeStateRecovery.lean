import Foundation.Crypto.Logic.Polygraph.NativeStateRoundtrip
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryObstruction

/-! For the fixed forward maximal state kernel, every reverse kernel using
only the intermediate state fails to restore some reachable input state.
This excludes changing the reverse alone, not other forward kernels or
extensions of the retained state. -/
namespace CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Machine.NativePreparedState (State Result encode decode decode_encode)
open RoundtripAudit (first second stationary stationary_kernel)
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

def forward (message : Bool) (event : State → Prop) : State → PMF State :=
  (edgeTransition first second sharpTableChain_edge message event).kernel

theorem forward_encoded (message : Bool) (event : State → Prop) (result : Result) :
    forward message event (encode result) = (RecoveryObstruction.forward message result).map encode := by
  simp only [forward, edgeTransition, transition, EncodedMaximal.kernel, decode_encode,
    RecoveryObstruction.forward, Roundtrip.p, Roundtrip.q]

theorem shared_from_zero (message : Bool) (event : State → Prop) :
    encode (1,message) ∈ (forward message event (encode (0,message))).support := by
  rw [forward_encoded]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(1,message), RecoveryObstruction.shared_from_zero message, rfl⟩

theorem shared_from_two (message : Bool) (event : State → Prop) :
    encode (1,message) ∈ (forward message event (encode (2,!message))).support := by
  rw [forward_encoded]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(1,message), RecoveryObstruction.shared_from_two message, rfl⟩

theorem two_source_reachable (message : Bool) :
    encode (2,!message) ∈ (nativeLaw first message).support := by
  rw [nativeLaw_eq]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(2,!message), RecoveryObstruction.two_source_supported message, rfl⟩

theorem no_reverse (message : Bool) (event : State → Prop) :
    ¬ ∃ reverse, KernelRecovery.RecoversOn (forward message event) reverse
      (fun state => state ∈ (nativeLaw first message).support) := by
  apply KernelRecovery.common_output_no_recovery (forward message event) _
    (encode (0,message)) (encode (2,!message)) (RoundtripAudit.source_reachable message) (two_source_reachable message)
    (by
      intro same
      have resultSame := Machine.NativePreparedState.encode_injective same
      exact (by decide : (0 : Fin 5) ≠ 2) (congrArg Prod.fst resultSame))
    (encode (1,message)) (shared_from_zero message event) (shared_from_two message event)

theorem no_reverse_path_cell (message : Bool) (event : State → Prop)
    (reverse : Path (game second message event) (game first message event)) :
    ¬ Nonempty (Cell4
      (.seq (.step (edgeTransition first second sharpTableChain_edge message event)) reverse)
      (stationary message event)) := by
  rintro ⟨cell⟩
  apply no_reverse message event
  refine ⟨reverse.kernel, ?_⟩
  intro state _
  have same := cell.sound.kernel_eq state
  rw [stationary_kernel] at same
  exact same

theorem no_reverse_path_edits (message : Bool) (event : State → Prop)
    (reverse : Path (game second message event) (game first message event)) :
    ¬ Nonempty (DiagramBridge.Edits
      (DiagramBridge.diagram (.seq (.step (edgeTransition first second sharpTableChain_edge message event)) reverse))
      (DiagramBridge.diagram (stationary message event))) := by
  rintro ⟨edits⟩
  have cell := DiagramBridge.edit_comparison edits
  rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram] at cell
  exact no_reverse_path_cell message event reverse ⟨cell⟩

end
end CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit
