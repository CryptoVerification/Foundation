import Foundation.Crypto.Logic.Polygraph.NativeStateCoherence
import Foundation.Crypto.Semantics.Probability.ClassicalBitRoundtripKernel

/-! Audit a concrete composition of the already selected native-state kernels.
The round trip preserves the endpoint law but is not an identity correspondence,
even after giving the identity path the same conservative loss budget. -/
namespace CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Machine.NativePreparedState (State Result encode decode decode_encode)
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev first : Vertex := sharpTableChain 0
abbrev second : Vertex := sharpTableChain 2

theorem reverse_edge : faceEdge (orderedGridComplex 32) second first := by
  obtain ⟨different, cell, hc, hf, hs⟩ := sharpTableChain_edge
  exact ⟨Ne.symm different, cell, hc, hs, hf⟩

def loop (message : Bool) (event : State → Prop) :
    Path (game first message event) (game first message event) :=
  .seq (.step (edgeTransition first second sharpTableChain_edge message event))
    (.step (edgeTransition second first reverse_edge message event))

theorem loop_preserves (message : Bool) (event : State → Prop) :
    (nativeLaw first message).bind (loop message event).kernel = nativeLaw first message :=
  (loop message event).preserve

theorem loop_loss (message : Bool) (event : State → Prop) : (loop message event).loss = 37 / 64 := by
  change (37 / 128 : ℝ≥0∞) + 37 / 128 = 37 / 64
  rw [ENNReal.div_add_div_same, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem kernel_encoded (message : Bool) (event : State → Prop) (result : Result) :
    (loop message event).kernel (encode result) = (Roundtrip.roundtrip message result).map encode := by
  simp only [loop, Path.kernel, edgeTransition, transition, EncodedMaximal.kernel,
    decode_encode, PMF.bind_map, PMF.map_bind, Function.comp_def, Roundtrip.roundtrip, Roundtrip.p, Roundtrip.q]

theorem kernel_recovered (message : Bool) (event : State → Prop) (result : Result) :
    ((loop message event).kernel (encode result)).map decode = Roundtrip.roundtrip message result := by
  rw [kernel_encoded, PMF.map_comp]
  have h : decode ∘ encode = id := funext decode_encode
  rw [h, PMF.map_id]

theorem source_reachable (message : Bool) : encode (0,message) ∈ (nativeLaw first message).support := by
  rw [nativeLaw_eq]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(0,message), Roundtrip.source_supported message, rfl⟩

theorem changes_key (message : Bool) (event : State → Prop) :
    (((loop message event).kernel (encode (0,message))).map decode (2,!message)).toReal = 85 / 592 := by
  rw [kernel_recovered]
  exact Roundtrip.changes_key message

def paddedIdentityStep (message : Bool) (event : State → Prop) :
    Step (game first message event) (game first message event) :=
  { Step.ofMap _ _ id (PMF.map_id _) (fun _ _ => Iff.rfl) with
    loss := 37 / 64
    bound := by
      change eventProb _ (fun _ => False) ≤ _
      simp [eventProb] }

def stationary (message : Bool) (event : State → Prop) :
    Path (game first message event) (game first message event) := .step (paddedIdentityStep message event)

theorem stationary_kernel (message : Bool) (event : State → Prop) (s : State) :
    (stationary message event).kernel s = PMF.pure s := rfl

theorem same_loss (message : Bool) (event : State → Prop) :
    (loop message event).loss = (stationary message event).loss := loop_loss message event

theorem no_cell (message : Bool) (event : State → Prop) :
    ¬ Nonempty (Cell4 (loop message event) (stationary message event)) := by
  rintro ⟨cell⟩
  have h := congrArg (fun law => law.map decode) (cell.sound.kernel_eq (encode (0,message)))
  rw [kernel_recovered, stationary_kernel, PMF.pure_map, decode_encode] at h
  exact Roundtrip.not_identity message h

theorem no_reverse_cell (message : Bool) (event : State → Prop) :
    ¬ Nonempty (Cell4 (stationary message event) (loop message event)) := by
  rintro ⟨cell⟩
  exact no_cell message event ⟨cell.symm⟩

theorem no_diagram_edits (message : Bool) (event : State → Prop) :
    ¬ Nonempty (DiagramBridge.Edits (DiagramBridge.diagram (loop message event))
      (DiagramBridge.diagram (stationary message event))) := by
  rintro ⟨edits⟩
  have cell := DiagramBridge.edit_comparison edits
  rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram] at cell
  exact no_cell message event ⟨cell⟩

end
end CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit
