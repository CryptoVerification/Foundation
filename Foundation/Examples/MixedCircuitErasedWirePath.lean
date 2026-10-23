import Foundation.Crypto.Logic.Polygraph.MixedCircuitWirePathContracts
import Foundation.Examples.MixedCircuitMACWirePass

/-! A genuine erased eighteen-law wire root: identity on the unit shape
normalizes by unitIdentity, while discard is already canonical. The residual
is the empty path, not a synthetic identity rewrite. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ErasedWirePath
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Stateful.WiringUnion
open WirePass
set_option backward.isDefEq.respectTransparency false

def sourceRules (_ : Unit) : Relator signature where
  inputs := .unit
  outputs := .unit
  left := .wire (.identity .unit)
  right := .wire (.discard .unit)
  extra := ∅
  balanced := rfl

def unitStep : Step (rules MAC.relators) (sourceRules ()).left (sourceRules ()).right :=
  wireStep (Cartesian.Step.root Cartesian.Root.unitIdentity)

theorem identity_witness :
    witness (original := MAC.relators) (sourceRules ()).left = .step unitStep := rfl

theorem discard_witness :
    witness (original := MAC.relators) (sourceRules ()).right = .refl (sourceRules ()).right := rfl

def contract : PathResidual.Contract sourceRules MAC.relators where
  embed _ := unitStep
  residual _ := .refl (sourceRules ()).right
  square _ := .refl (.comp (.step unitStep) (.refl (sourceRules ()).right))
  embed_support _ := rfl
  residual_covered _ := by simp [sourceRules, output_needs, RewriteTrack.support, Primitive.support, Relator.support, Circuit.needs]
  square_support _ := rfl

theorem residual_is_empty : contract.residual () = .refl (sourceRules ()).right := rfl

def framedChange (stage : Nat) :=
  Step.tensorLeft (Step.root (Primitive.rule (relators := sourceRules) ())) (MAC.before stage)

theorem framed_residual_is_empty (stage : Nat) :
    PathResidual.residualStep contract (framedChange stage) =
      .refl (output (.tensor (sourceRules ()).right (MAC.before stage))) := rfl

theorem framed_residual_support (stage : Nat) :
    RewriteTrack.support (PathResidual.residualStep contract (framedChange stage)) = {stage} := by
  rw [framed_residual_is_empty]
  simp [RewriteTrack.support, output_needs, sourceRules, Circuit.needs, MAC.before, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout]

def framedSquare (stage : Nat) := PathResidual.exactTrackSquare contract (.step (framedChange stage))

theorem framed_support (stage : Nat) : Homotopy.support (framedSquare stage).val = {stage} := by
  rw [(framedSquare stage).property]
  simp [framedChange, RewriteTrack.support, Step.support, Primitive.support, Relator.support, sourceRules,
    Circuit.needs, MAC.before, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout]

def combinedRules : Nat ⊕ Unit → Relator signature
  | .inl stage => MAC.relators stage
  | .inr _ => sourceRules ()

def combinedContract : PathResidual.Contract combinedRules MAC.relators where
  embed label := match label with
    | .inl stage => Stateful.WiringUnion.embedStep (MAC.rewrite stage)
    | .inr _ => contract.embed ()
  residual label := match label with
    | .inl stage => .step (WirePassNaturality.contract.residual stage)
    | .inr _ => contract.residual ()
  square label := by
    cases label with
    | inl stage => exact WirePassNaturality.contract.square stage
    | inr _ => exact contract.square ()
  embed_support label := by cases label <;> rfl
  residual_covered label := by
    cases label with
    | inl stage => exact (WirePassNaturality.contract.support_eq stage).le
    | inr _ => exact contract.residual_covered ()
  square_support label := by
    cases label with
    | inl stage => exact WirePassNaturality.root_support stage
    | inr _ => exact contract.square_support ()

def mixedPath (stage : Nat) : RewriteTrack (relators := combinedRules)
    (.tensor (MAC.before stage) (sourceRules ()).left) (.tensor (MAC.after stage) (sourceRules ()).right) :=
  .comp (.step (.tensorLeft (.root (Primitive.rule (relators := combinedRules) (Sum.inl stage))) (sourceRules ()).left))
    (.step (.tensorRight (MAC.after stage) (.root (Primitive.rule (relators := combinedRules) (Sum.inr ())))))

theorem mixed_residual (stage : Nat) : PathResidual.residualTrack combinedContract (mixedPath stage) =
    .comp (.step (.tensorLeft (Stateful.WiringUnion.embedStep (MAC.rewrite stage)) (sourceRules ()).right))
      (.refl (Circuit.tensor (MAC.after stage) (sourceRules ()).right)) := rfl

def mixedSquare (stage : Nat) := PathResidual.exactTrackSquare combinedContract (mixedPath stage)

theorem mixed_support (stage : Nat) : Homotopy.support (mixedSquare stage).val = {stage, stage + 1} := by
  rw [(mixedSquare stage).property]
  simp [mixedPath, combinedRules, RewriteTrack.support, Step.support, Primitive.support, Relator.support,
    sourceRules, Circuit.needs, MAC.relators, MAC.before, MAC.after, MAC.signature,
    CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout]

def copyDiscardWire : Wiring signature (.pair MAC.finish .unit) (.pair MAC.finish .unit) :=
  .seq (.seq (.copy _) (.tensor (.identity _) (.discard _))) (.rightUnit _)

def copyDiscardPath (stage : Nat) :=
  (Placement.seqLeft (Circuit.wire copyDiscardWire)).track (mixedPath stage)

def copyDiscardSquare (stage : Nat) := PathResidual.exactTrackSquare combinedContract (copyDiscardPath stage)

theorem copy_discard_support (stage : Nat) : Homotopy.support (copyDiscardSquare stage).val = {stage, stage + 1} := by
  rw [(copyDiscardSquare stage).property]
  have sourceSupport : RewriteTrack.support (mixedPath stage) = {stage, stage + 1} :=
    (mixedSquare stage).property.symm.trans (mixed_support stage)
  simp only [copyDiscardPath, Placement.track_support, sourceSupport, Placement.needs, Circuit.needs, Finset.union_empty]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ErasedWirePath
