import Foundation.Crypto.Logic.Polygraph.NativeRetainedTransition

/-! Native and table presentations of the same labelled statistical
transition agree on conditional kernels, not merely endpoint probabilities. -/
namespace CryptoLogic.Polygraph.Experiment.NativeRetained
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

def referenceGame (v : Vertex) (message : Bool) (event : Result → Prop) : Observed :=
  FiniteMaximal.game (tableEightBitLaw v message) event

def toReference (v : Vertex) (message : Bool) (event : Result → Prop) :
    Step (game v message event) (referenceGame v message event) :=
  Step.ofMap _ _ id (by
    change (nativeLaw v message).map id = tableEightBitLaw v message
    rw [PMF.map_id, nativeLaw_eq])
    (fun _ _ => Iff.rfl)

def fromReference (v : Vertex) (message : Bool) (event : Result → Prop) :
    Step (referenceGame v message event) (game v message event) :=
  Step.ofMap _ _ id (by
    change (tableEightBitLaw v message).map id = nativeLaw v message
    rw [PMF.map_id, nativeLaw_eq])
    (fun _ _ => Iff.rfl)

def direct (u v : Vertex) (message : Bool) (event : Result → Prop) :
    Path (game u message event) (game v message event) := .step (transition u v message event)

def factored (u v : Vertex) (message : Bool) (event : Result → Prop) :
    Path (game u message event) (game v message event) :=
  .seq (.step (toReference u message event))
    (.seq (.step (FiniteMaximal.step (tableEightBitLaw u message) (tableEightBitLaw v message) event))
      (.step (fromReference v message event)))

theorem factorization_kernel (u v : Vertex) (message : Bool) (event : Result → Prop) (x : Result) :
    (direct u v message event).kernel x = (factored u v message event).kernel x := by
  simp only [direct, factored, Path.kernel, toReference, fromReference, Step.ofMap,
    PMF.pure_bind, id_eq, PMF.bind_pure]
  change FiniteMaximalCoupling.kernel (nativeLaw u message) (nativeLaw v message) x =
    FiniteMaximalCoupling.kernel (tableEightBitLaw u message) (tableEightBitLaw v message) x
  rw [nativeLaw_eq, nativeLaw_eq]

theorem factorization_loss (u v : Vertex) (message : Bool) (event : Result → Prop) :
    (direct u v message event).loss = (factored u v message event).loss := by
  change ENNReal.ofReal (finiteVariation (nativeLaw u message) (nativeLaw v message)) =
    0 + (ENNReal.ofReal (finiteVariation (tableEightBitLaw u message) (tableEightBitLaw v message)) + 0)
  rw [nativeLaw_eq, nativeLaw_eq, add_zero, zero_add]

def factorizationCell (u v : Vertex) (message : Bool) (event : Result → Prop) :
    Cell4 (direct u v message event) (factored u v message event) :=
  .generator ⟨factorization_kernel u v message event, factorization_loss u v message event⟩

def factorizationEdit (u v : Vertex) (message : Bool) (event : Result → Prop) :
    DiagramBridge.Edit (DiagramBridge.diagram (direct u v message event))
      (DiagramBridge.diagram (factored u v message event)) :=
  .game (by
    rw [DiagramBridge.evaluate_diagram, DiagramBridge.evaluate_diagram]
    exact factorizationCell u v message event)

def contextualFactorization {before after : Observed} (u v : Vertex) (message : Bool)
    (event : Result → Prop) (beforePath : Path before (game u message event))
    (afterPath : Path (game v message event) after) :
    Cell4 (.seq (.seq beforePath (direct u v message event)) afterPath)
      (.seq (.seq beforePath (factored u v message event)) afterPath) :=
  .seq (.seq (.refl beforePath) (factorizationCell u v message event)) (.refl afterPath)

end
end CryptoLogic.Polygraph.Experiment.NativeRetained
