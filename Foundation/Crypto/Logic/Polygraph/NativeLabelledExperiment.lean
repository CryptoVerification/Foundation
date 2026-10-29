import Foundation.Crypto.Logic.Polygraph.NativePreparedExperiment
import Foundation.Crypto.Semantics.Machine.NativePreparedJointResult

/-! A retained-state interpretation with both the public packet and labelled
internal result from one native execution. Forgetting the private projection
is directed. The square relating native realization and forgetting has a
pointwise kernel/loss certificate in the existing four-cell language. -/
namespace CryptoLogic.Polygraph.Experiment.NativePrepared.Labelled
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

abbrev Output := Machine.NativePreparedJointResult.Output

def bounded : CryptoLogic.BoundedProgram := Machine.NativePreparedKeyDecision.bounded

def publicView (output : Output) : NativePrepared.Output := some output.1

noncomputable def native (v : OrderedGridVertex 32) (message : Bool) : Program Output :=
  .sample ((Machine.evalConfigWithin bounded.program
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput v message)) 930).map
      Machine.NativePreparedJointResult.observe)

noncomputable def reference (v : OrderedGridVertex 32) (message : Bool) : Program Output :=
  .sample ((tableEightBitLaw v message).map Machine.NativePreparedJointResult.encode)

theorem same_machine : bounded.program = NativePrepared.bounded.program := rfl

theorem executable (input : List Bool) : Machine.HaltsWithin bounded.program input 930 :=
  Machine.NativePreparedKeyDecision.haltsWithin input

theorem native_law (v : OrderedGridVertex 32) (message : Bool) :
    (native v message).eval = (reference v message).eval := Machine.NativePreparedJointResult.initial_law v message

theorem labelled_marginal (v : OrderedGridVertex 32) (message : Bool) :
    (native v message).eval.map Prod.snd = (tableEightBitLaw v message).map some := by
  rw [native_law]
  change (((tableEightBitLaw v message).map Machine.NativePreparedJointResult.encode).map Prod.snd) = _
  rw [PMF.map_comp]
  rfl

noncomputable def exactStep (v : OrderedGridVertex 32) (message : Bool) :
    ExactStep (native v message) (reference v message) := .distribution (native_law v message)

noncomputable def exactPath (v : OrderedGridVertex 32) (message : Bool) :
    ExactPath (native v message) (reference v message) := .step (exactStep v message)

noncomputable def exactHop (v : OrderedGridVertex 32) (message : Bool) (event : Output → Prop) :
    Hop ⟨Output, native v message, event⟩ ⟨Output, reference v message, event⟩ 0 :=
  .exact (exactPath v message) event

noncomputable def contextPath {A : Type} (v : OrderedGridVertex 32) (message : Bool)
    (next : Output → Program A) :
    ExactPath (.bind (native v message) next) (.bind (reference v message) next) :=
  .step (.bindFirst (exactStep v message) next)

theorem public_native (v : OrderedGridVertex 32) (message : Bool) :
    (native v message).eval.map publicView = (NativePrepared.native v message).eval := by
  rw [native_law, NativePrepared.native_law]
  change (((tableEightBitLaw v message).map Machine.NativePreparedJointResult.encode).map publicView) = _
  rw [PMF.map_comp]
  rfl

theorem public_reference (v : OrderedGridVertex 32) (message : Bool) :
    (reference v message).eval.map publicView = (NativePrepared.reference v message).eval := by
  change (((tableEightBitLaw v message).map Machine.NativePreparedJointResult.encode).map publicView) = _
  rw [PMF.map_comp]
  rfl

noncomputable def nativeGame (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Output, native v message, fun output => Machine.NativePreparedKeyDecision.acceptedPacket (publicView output)⟩

noncomputable def referenceGame (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Output, reference v message, fun output => Machine.NativePreparedKeyDecision.acceptedPacket (publicView output)⟩

noncomputable def direct (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Path (nativeGame v message) (referenceGame v message) :=
  .step (GameCoherence.Step.exact (exactPath v message) _)

noncomputable def forgetNative (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Step (nativeGame v message) (NativePrepared.nativeGame v message) :=
  .ofMap _ _ publicView (public_native v message) (fun _ _ => Iff.rfl)

noncomputable def forgetReference (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Step (referenceGame v message) (NativePrepared.referenceGame v message) :=
  .ofMap _ _ publicView (public_reference v message) (fun _ _ => Iff.rfl)

noncomputable def realizeThenForget (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Path (nativeGame v message) (NativePrepared.referenceGame v message) :=
  .seq (direct v message) (.step (forgetReference v message))

noncomputable def forgetThenRealize (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Path (nativeGame v message) (NativePrepared.referenceGame v message) :=
  .seq (.step (forgetNative v message)) (NativePrepared.direct v message)

noncomputable def forgetSquare (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Cell4 (realizeThenForget v message) (forgetThenRealize v message) := .generator (by
  constructor
  · intro output
    change ((PMF.pure output).bind (fun value => PMF.pure (publicView value))) =
      (PMF.pure (publicView output)).bind PMF.pure
    simp only [PMF.pure_bind]
  · rfl)

noncomputable def forgetEdit (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.DiagramBridge.Edit
      (GameCoherence.DiagramBridge.diagram (realizeThenForget v message))
      (GameCoherence.DiagramBridge.diagram (forgetThenRealize v message)) := .game (by
  rw [GameCoherence.DiagramBridge.evaluate_diagram, GameCoherence.DiagramBridge.evaluate_diagram]
  exact forgetSquare v message)

theorem forgetting_kernel (v : OrderedGridVertex 32) (message : Bool) (output : Output) :
    (realizeThenForget v message).kernel output = (forgetThenRealize v message).kernel output :=
  (forgetSquare v message).sound.kernel_eq output

theorem forgetting_loss (v : OrderedGridVertex 32) (message : Bool) :
    (realizeThenForget v message).loss = (forgetThenRealize v message).loss := (forgetSquare v message).sound.loss_eq

noncomputable def labelledStep (v : OrderedGridVertex 32) (message : Bool) (event : Option (Fin 5 × Bool) → Prop) :
    GameCoherence.Step
      ⟨Output, native v message, fun output => event output.2⟩
      ⟨Option (Fin 5 × Bool), .sample ((tableEightBitLaw v message).map some), event⟩ :=
  .ofMap _ _ Prod.snd (labelled_marginal v message) (fun _ _ => Iff.rfl)

end CryptoLogic.Polygraph.Experiment.NativePrepared.Labelled
