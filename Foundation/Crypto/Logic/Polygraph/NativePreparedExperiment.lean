import Foundation.Crypto.Semantics.Machine.NativePreparedKeyDecision
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation
import Foundation.Crypto.Logic.Polygraph.GameCoherenceDiagram

/-! Native realization of the existing experiment and inference-diagram syntax.
Exact changes preserve the complete returned packet. The four-cell compares
the direct interpretation with the checked preparation/callee factorization.
Context lifting is semantic; arbitrary logical continuations acquire no free
native execution or runtime certificate. -/
namespace CryptoLogic.Polygraph.Experiment.NativePrepared
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

abbrev Output := Option (List Bool)

noncomputable def native (v : OrderedGridVertex 32) (message : Bool) : Program Output :=
  .sample (Machine.evalWithin Machine.NativePreparedKeyDecision.code
    (Machine.NativePreparedKeyDecision.rawInput v message) 930)

noncomputable def callee (v : OrderedGridVertex 32) (message : Bool) : Program Output :=
  .sample (Machine.evalWithin Machine.NativeKeyPairDecisionExecution.code
    (List.ofFn (Machine.EightBitCipherControl.request v message)) 442)

noncomputable def reference (v : OrderedGridVertex 32) (message : Bool) : Program Output :=
  .sample ((tableEightBitLaw v message).map (fun result => some [!result.2, keyPairTest result]))

def bounded : CryptoLogic.BoundedProgram := Machine.NativePreparedKeyDecision.bounded

theorem input_length (v : OrderedGridVertex 32) (message : Bool) :
    (Machine.NativePreparedKeyDecision.rawInput v message).length = 39 :=
  Machine.NativePreparedKeyDecision.rawInput_length v message

theorem budget (n : ℕ) : bounded.budget n = 930 := rfl

theorem executable (input : List Bool) : Machine.HaltsWithin bounded.program input 930 :=
  Machine.NativePreparedKeyDecision.haltsWithin input

theorem native_realization (v : OrderedGridVertex 32) (message : Bool) :
    Machine.evalWithin bounded.program (Machine.NativePreparedKeyDecision.rawInput v message)
      (bounded.budget 39) = (native v message).eval := rfl

theorem callee_law (v : OrderedGridVertex 32) (message : Bool) :
    (callee v message).eval = (reference v message).eval := by
  unfold callee reference
  change Machine.evalWithin Machine.NativeKeyPairDecisionExecution.code
    (List.ofFn (Machine.EightBitCipherControl.request v message)) 442 = _
  rw [Machine.NativeKeyPairOutputPacket.evalWithin_of_halts _ _ _
    (Machine.NativeKeyPairDecisionExecution.haltsWithin _)]
  change (Machine.evalConfigWithin Machine.NativeKeyPairDecisionExecution.code
    (Machine.Configuration.initial (List.ofFn (Machine.EightBitCipherControl.request v message))) 442).map
    (some ∘ Machine.Configuration.outputBits) = _
  rw [← PMF.map_comp,
    Machine.evalConfigWithin_map_eq_of_equivalent _ _ _
      (Machine.NativeControlledCipherInitial.entry_equivalent v message).symm 442 _ (fun _ _ h => h.outputBits),
    Machine.NativeKeyPairOutputPacket.framed_packet, PMF.map_comp]
  rfl

theorem native_law (v : OrderedGridVertex 32) (message : Bool) :
    (native v message).eval = (reference v message).eval :=
  Machine.NativePreparedKeyDecision.evalWithin_law v message

theorem preparation_law (v : OrderedGridVertex 32) (message : Bool) :
    (native v message).eval = (callee v message).eval :=
  (native_law v message).trans (callee_law v message).symm

noncomputable def directStep (v : OrderedGridVertex 32) (message : Bool) :
    ExactStep (native v message) (reference v message) := .distribution (native_law v message)

noncomputable def preparationStep (v : OrderedGridVertex 32) (message : Bool) :
    ExactStep (native v message) (callee v message) := .distribution (preparation_law v message)

noncomputable def calleeStep (v : OrderedGridVertex 32) (message : Bool) :
    ExactStep (callee v message) (reference v message) := .distribution (callee_law v message)

noncomputable def exactPath (v : OrderedGridVertex 32) (message : Bool) :
    ExactPath (native v message) (reference v message) := .step (directStep v message)

noncomputable def contextPath {A : Type} (v : OrderedGridVertex 32) (message : Bool)
    (next : Output → Program A) :
    ExactPath (.bind (native v message) next) (.bind (reference v message) next) :=
  .step (.bindFirst (directStep v message) next)

noncomputable def contextHop {A : Type} (v : OrderedGridVertex 32) (message : Bool)
    (next : Output → Program A) (event : A → Prop) :
    Hop ⟨A, .bind (native v message) next, event⟩ ⟨A, .bind (reference v message) next, event⟩ 0 :=
  .exact (contextPath v message next) event

noncomputable def contextDiagram {A : Type} (v : OrderedGridVertex 32) (message : Bool)
    (next : Output → Program A) (event : A → Prop) := Statistical.diagram (contextHop v message next event)

theorem context_sound {A : Type} (v : OrderedGridVertex 32) (message : Bool)
    (next : Output → Program A) (event : A → Prop) :
    probabilityGap
      (eventProb ((native v message).eval.bind (fun output => (next output).eval)) event)
      (eventProb ((reference v message).eval.bind (fun output => (next output).eval)) event) ≤ 0 :=
  Statistical.sound (contextHop v message next event)

noncomputable def nativeGame (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Output, native v message, Machine.NativePreparedKeyDecision.acceptedPacket⟩

noncomputable def calleeGame (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Output, callee v message, Machine.NativePreparedKeyDecision.acceptedPacket⟩

noncomputable def referenceGame (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Output, reference v message, Machine.NativePreparedKeyDecision.acceptedPacket⟩

noncomputable def direct (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Path (nativeGame v message) (referenceGame v message) :=
  .step (GameCoherence.Step.exact (exactPath v message) _)

noncomputable def factored (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Path (nativeGame v message) (referenceGame v message) :=
  .seq (.step (GameCoherence.Step.exact (.step (preparationStep v message)) _))
    (.step (GameCoherence.Step.exact (.step (calleeStep v message)) _))

noncomputable def factorizationCell (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.Cell4 (direct v message) (factored v message) := .generator (by
  constructor
  · intro output
    change PMF.pure output = (PMF.pure output).bind PMF.pure
    exact (PMF.pure_bind _ _).symm
  · change (0 : ℝ≥0∞) = 0 + 0
    simp)

noncomputable def directDiagram (v : OrderedGridVertex 32) (message : Bool) :=
  GameCoherence.DiagramBridge.diagram (direct v message)

noncomputable def factoredDiagram (v : OrderedGridVertex 32) (message : Bool) :=
  GameCoherence.DiagramBridge.diagram (factored v message)

noncomputable def factorizationEdit (v : OrderedGridVertex 32) (message : Bool) :
    GameCoherence.DiagramBridge.Edit (directDiagram v message) (factoredDiagram v message) := .game (by
  rw [directDiagram, factoredDiagram, GameCoherence.DiagramBridge.evaluate_diagram,
    GameCoherence.DiagramBridge.evaluate_diagram]
  exact factorizationCell v message)

theorem factorization_kernel (v : OrderedGridVertex 32) (message : Bool) (output : Output) :
    (direct v message).kernel output = (factored v message).kernel output :=
  (factorizationCell v message).sound.kernel_eq output

theorem factorization_loss (v : OrderedGridVertex 32) (message : Bool) :
    (direct v message).loss = (factored v message).loss := (factorizationCell v message).sound.loss_eq

theorem direct_loss (v : OrderedGridVertex 32) (message : Bool) : (direct v message).loss = 0 := rfl

noncomputable def contextualFactorization {before after : Observed}
    (v : OrderedGridVertex 32) (message : Bool)
    (beforePath : GameCoherence.Path before (nativeGame v message))
    (afterPath : GameCoherence.Path (referenceGame v message) after) :
    GameCoherence.Cell4
      (.seq (.seq beforePath (direct v message)) afterPath)
      (.seq (.seq beforePath (factored v message)) afterPath) :=
  .seq (.seq (.refl beforePath) (factorizationCell v message)) (.refl afterPath)

theorem contextual_retained_law {before after : Observed} (v : OrderedGridVertex 32) (message : Bool)
    (beforePath : GameCoherence.Path before (nativeGame v message))
    (afterPath : GameCoherence.Path (referenceGame v message) after)
    {A : Type} (observe : after.Outcome → A) (initial : before.Outcome) :
    ((GameCoherence.Path.seq (.seq beforePath (direct v message)) afterPath).kernel initial).map observe =
      ((GameCoherence.Path.seq (.seq beforePath (factored v message)) afterPath).kernel initial).map observe :=
  (contextualFactorization v message beforePath afterPath).retained_law observe initial

end CryptoLogic.Polygraph.Experiment.NativePrepared
