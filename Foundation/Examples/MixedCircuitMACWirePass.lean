import Foundation.Crypto.Logic.Polygraph.MixedCircuitWirePassContracts
import Foundation.Examples.MixedCircuitMAC

/-! The original MAC contraction supplies an actual root contract. Its
normalized residual is the same root, not a whole-path conjugation. Contextual
and whole-track squares are generated without new higher generators. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.WirePassNaturality
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Stateful.WiringUnion
open WirePass
set_option backward.isDefEq.respectTransparency false

def contract : RootCompatibility MAC.relators where
  residual stage := embedStep (MAC.rewrite stage)
  square stage :=
    (Four.rightUnit (.step (embedStep (MAC.rewrite stage)))).trans
      ((Four.leftUnit (.step (embedStep (MAC.rewrite stage)))).symm.trans
        (Four.comp (Four.leftUnit (.refl (MAC.before stage))).symm
          (.refl (.step (embedStep (MAC.rewrite stage))))))
  support_eq _ := rfl

def contextual {a b} {p q : Circuit signature a b} (change : Step MAC.relators p q) :=
  WirePass.square contract change

def wholeTrack {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := MAC.relators) p q) :=
  WirePass.trackSquare contract path

def copyDiscardChange (stage : Nat) :=
  Step.tensorLeft (MAC.copiedRewrite stage) (Circuit.wire (signature := signature) (Wire.discard MAC.finish))

def copyDiscardSquare (stage : Nat) := contextual (copyDiscardChange stage)

theorem normalized_residual_support {a b} {p q : Circuit signature a b} (change : Step MAC.relators p q) :
    (WirePass.residual contract change).support = change.support := residual_support contract change

theorem root_support (stage : Nat) :
    Homotopy.support (contract.square stage) = (Primitive.rule (relators := MAC.relators) stage).support := by
  change Homotopy.support (contract.square stage) = (MAC.rewrite stage).support
  simp only [contract, Homotopy.support, RewriteTrack.support, embedStep_support]
  ext label
  have covered : label ∈ (MAC.before stage).needs → label ∈ (MAC.rewrite stage).support :=
    fun member => (MAC.rewrite stage).boundaries.1 member
  simp only [Finset.mem_union] at *
  tauto

def exactWholeTrack {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := MAC.relators) p q) :=
  WirePass.exactTrackSquare contract root_support path

theorem copy_discard_square_support (stage : Nat) :
    Homotopy.support (copyDiscardSquare stage) = {stage, stage + 1} := by
  rw [copyDiscardSquare, contextual, WirePass.square_support contract root_support]
  simpa only [copyDiscardChange, Step.support, Circuit.needs, Finset.union_empty] using MAC.copied_support stage

/-- This joint law is a semantic application of the generated witness. It
does not compare native programs or assert a new MAC advantage bound. -/
theorem repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := MAC.relators) p q)
    (changed : Finset Nat)
    (cached : Holds old path.support)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated
      (fresh path.support changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : Holds updated p.needs,
    ∃ right : Holds updated (WirePass.output q).needs,
      law.bind (fun past => (Stateful.evaluate model.base p left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (WirePass.output q) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let proof := exactWholeTrack path
  have valid : Holds updated (Homotopy.support proof.val) := by
    rw [proof.property]
    exact repair cached unchanged rechecked
  let boundary := valid.restrict (Homotopy.boundaries proof.val).1
  refine ⟨boundary.restrict (RewriteTrack.boundaries (.comp (embedTrack path) (WirePass.witness q))).1,
    boundary.restrict (RewriteTrack.boundaries (.comp (embedTrack path) (WirePass.witness q))).2, ?_⟩
  exact Stateful.track_joint (Stateful.WiringUnion.checked model)
    (.comp (embedTrack path) (WirePass.witness q)) boundary _ _ law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.WirePassNaturality
