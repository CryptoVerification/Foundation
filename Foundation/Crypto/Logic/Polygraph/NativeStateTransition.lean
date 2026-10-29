import Foundation.Crypto.Logic.Polygraph.EncodedMaximalStep
import Foundation.Crypto.Semantics.Machine.NativePreparedState
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitObserverBound

/-! Statistical transformations of the complete native cell state, modulo
only redundant blank padding. Both tapes, program counter and halt flag are
retained. Coupling construction is semantic, with no new sampler runtime. -/
namespace CryptoLogic.Polygraph.Experiment.NativeState
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
open Machine.NativePreparedState (State Result encode decode decode_encode)
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Vertex := OrderedGridVertex 32

def nativeLaw (v : Vertex) (message : Bool) : PMF State :=
  (Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map
      Machine.NativePreparedState.state

theorem nativeLaw_eq (v : Vertex) (message : Bool) :
    nativeLaw v message = (tableEightBitLaw v message).map encode := Machine.NativePreparedState.initial_law v message

abbrev game (v : Vertex) (message : Bool) (event : State → Prop) : Observed :=
  ⟨State, .sample (nativeLaw v message), event⟩

def transition (u v : Vertex) (message : Bool) (event : State → Prop) :
    Step (game u message event) (game v message event) where
  kernel := EncodedMaximal.kernel encode decode (tableEightBitLaw u message) (tableEightBitLaw v message)
  preserve := by
    change (nativeLaw u message).bind _ = nativeLaw v message
    rw [nativeLaw_eq, nativeLaw_eq]
    exact EncodedMaximal.preserve encode decode decode_encode _ _
  bad pair := pair.1 ≠ pair.2
  agree x _ y _ good := by
    have same : x = y := not_ne_iff.mp good
    subst y
    rfl
  loss := ENNReal.ofReal (finiteVariation (tableEightBitLaw u message) (tableEightBitLaw v message))
  bound := by
    change eventProb ((nativeLaw u message).bind fun x =>
      (EncodedMaximal.kernel encode decode (tableEightBitLaw u message) (tableEightBitLaw v message) x).map
        fun y => (x,y)) (fun pair => pair.1 ≠ pair.2) ≤ _
    rw [nativeLaw_eq, EncodedMaximal.joint_eq encode decode decode_encode,
      EncodedMaximal.mismatch_probability encode decode decode_encode]

theorem event_independent (u v : Vertex) (message : Bool) (e f : State → Prop) (x : State) :
    (transition u v message e).kernel x = (transition u v message f).kernel x := rfl

theorem loss_eq (u v : Vertex) (message : Bool) (event : State → Prop) :
    (transition u v message event).loss = ENNReal.ofReal (tableEightBitJointDistance u v message) := by
  change ENNReal.ofReal (finiteVariation _ _) = _
  rw [table_finiteVariation_eq]

def edgeTransition (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : State → Prop) : Step (game u message event) (game v message event) :=
  { transition u v message event with
    loss := 37 / 128
    bound := by
      apply (transition u v message event).bound.trans
      rw [loss_eq]
      have h := ENNReal.ofReal_le_ofReal (table_experiment_edge_upper u v edge message)
      have hc : ENNReal.ofReal (37 / 128 : ℝ) = (37 / 128 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      rwa [hc] at h }

def edgeDiagram (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : State → Prop) :=
  DiagramBridge.diagram (.step (edgeTransition u v edge message event))

theorem edge_sound (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : State → Prop) :
    probabilityGap (eventProb (nativeLaw u message) event) (eventProb (nativeLaw v message) event) ≤
      (37 / 128 : ℝ≥0∞) := (edgeTransition u v edge message event).hop.sound

end
end CryptoLogic.Polygraph.Experiment.NativeState
