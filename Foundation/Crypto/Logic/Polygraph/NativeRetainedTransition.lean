import Foundation.Crypto.Logic.Polygraph.FiniteMaximalStep
import Foundation.Crypto.Semantics.Machine.NativeFiveKeyRealization
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitObserverBound

/-! Directed statistical transformations retain the full labelled key and
ciphertext view of the 930-step native execution. Conditional kernels are
explicit and event independent. Other machine registers are not retained. -/
namespace CryptoLogic.Polygraph.Experiment.NativeRetained
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Result := Fin 5 × Bool
abbrev Vertex := OrderedGridVertex 32

def nativeLaw (v : Vertex) (message : Bool) : PMF Result :=
  ((Machine.evalConfigWithin Machine.NativePreparedKeyDecision.code
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map
      Machine.NativePreparedInternalResult.observe).map (fun result => result.getD (0,false))

theorem nativeLaw_eq (v : Vertex) (message : Bool) : nativeLaw v message = tableEightBitLaw v message := by
  unfold nativeLaw
  rw [Machine.NativePreparedInternalResult.initial_law, PMF.map_comp]
  exact PMF.map_id _

def game (v : Vertex) (message : Bool) (event : Result → Prop) : Observed :=
  FiniteMaximal.game (nativeLaw v message) event

def transition (u v : Vertex) (message : Bool) (event : Result → Prop) :
    Step (game u message event) (game v message event) :=
  FiniteMaximal.step (nativeLaw u message) (nativeLaw v message) event

theorem loss_eq (u v : Vertex) (message : Bool) (event : Result → Prop) :
    (transition u v message event).loss = ENNReal.ofReal (tableEightBitJointDistance u v message) := by
  change ENNReal.ofReal (finiteVariation (nativeLaw u message) (nativeLaw v message)) = _
  rw [nativeLaw_eq, nativeLaw_eq, table_finiteVariation_eq]

theorem event_independent (u v : Vertex) (message : Bool) (e f : Result → Prop) (x : Result) :
    (transition u v message e).kernel x = (transition u v message f).kernel x := rfl

def edgeTransition (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : Result → Prop) : Step (game u message event) (game v message event) :=
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
    (message : Bool) (event : Result → Prop) :=
  DiagramBridge.diagram (.step (edgeTransition u v edge message event))

theorem edge_sound (u v : Vertex) (edge : faceEdge (orderedGridComplex 32) u v)
    (message : Bool) (event : Result → Prop) :
    probabilityGap (eventProb (nativeLaw u message) event) (eventProb (nativeLaw v message) event) ≤
      (37 / 128 : ℝ≥0∞) := (edgeTransition u v edge message event).hop.sound

end
end CryptoLogic.Polygraph.Experiment.NativeRetained
