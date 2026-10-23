import Foundation.Examples.MixedCircuitWireFusionTrackNaturality
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.SequentialFusionWirePass
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
open WireFusionTrackNaturality
/-! Sequential fusion commutes with the actual wire-leaf pass. The pure
composition comparison is equality of the generated proof tracks, proved from
the recursive normalizer; no arbitrary higher root or backtracking residual
is added. Tensor fusion still has a distinct coherence obligation. -/
set_option backward.isDefEq.respectTransparency false
private theorem transport_seq {a b c : Shape signature.PortAtom}
    {p : Wiring signature a b} {q : Wiring signature b c}
    {first first' : TypedRouting.Layout a b} {second second' : TypedRouting.Layout b c}
    {target : TypedRouting.Layout a c}
    (one : Cartesian.Cell p (Cartesian.reify first)) (two : Cartesian.Cell q (Cartesian.reify second))
    (h1 : first = first') (h2 : second = second')
    (h : Cartesian.substitute first second = target) (h' : Cartesian.substitute first' second' = target) :
    (Cartesian.Cell.seq (h1 ▸ one) (h2 ▸ two)).trans
      (cast (congrArg (fun layout => Cartesian.Cell
        (Wire.seq (Cartesian.reify first') (Cartesian.reify second')) (Cartesian.reify layout)) h')
        (Cartesian.seqNormal first' second')) =
    (h ▸ (Cartesian.Cell.seq one two).trans (Cartesian.seqNormal first second)) := by
  cases h1
  cases h2
  cases h
  rfl
theorem seq_normalization {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    (Cartesian.Cell.seq (Cartesian.normalizeCell p) (Cartesian.normalizeCell q)).trans
      (WireFusionResidual.seqWire p q) = Cartesian.normalizeCell (Wire.seq p q) := by
  unfold WireFusionResidual.seqWire
  dsimp only [Cartesian.normalizeCell, Cartesian.normalize, Cartesian.Normalized.seq]
  apply transport_seq
  have same := Cartesian.normalize_layout (Wire.seq p q)
  change Cartesian.substitute (Cartesian.normalize p).layout (Cartesian.normalize q).layout = _ at same
  simpa only [Cartesian.normalize_layout] using same

theorem seq_normalization_track {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    Track.comp (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)
      (wireTrack (original := Structural.Fusion.rules) (WireFusionResidual.seqWire p q).toTrack) =
    Stateful.WiringUnion.normalize (original := Structural.Fusion.rules) (Wire.seq p q) := by
  have same := congrArg (fun proof : Cartesian.Cell (Wire.seq p q)
      (Cartesian.reify (TypedRouting.normal (Wire.seq p q))) =>
      wireTrack (original := Structural.Fusion.rules) proof.toTrack) (seq_normalization p q)
  simpa only [seqInner, Stateful.WiringUnion.normalize, Cartesian.Cell.toTrack,
    Cartesian.seqLeftTrack, Cartesian.seqRightTrack, wireTrack, Track.map,
    FourNaturality.map_map, edit] using same

def pasted {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    Cell
      (.comp (.step (seqFusion p q))
        (.comp (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)
          (wireTrack (original := Structural.Fusion.rules) (WireFusionResidual.seqWire p q).toTrack)))
      (.comp (WirePass.witness (original := Structural.Fusion.rules) (.seq (.wire p) (.wire q)))
        (WireFusionResidual.seqResidual p q)) :=
  (Four.assoc _ _ _).symm.trans
    ((Four.comp (normalizeSeq p q).val.symm
      (.refl (wireTrack (original := Structural.Fusion.rules) (WireFusionResidual.seqWire p q).toTrack))).trans
      (Four.assoc _ _ _))

theorem pasted_support {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    PresentedCell.support (pasted p q) = ∅ := by
  have both :
      RewriteTrack.support (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack) ∪
      RewriteTrack.support (wireTrack (original := Structural.Fusion.rules) (WireFusionResidual.seqWire p q).toTrack) = ∅ := by
    have supported := Stateful.WiringUnion.normalize_support
      (original := Structural.Fusion.rules) (Wire.seq p q)
    rw [← seq_normalization_track p q] at supported
    exact supported
  have inner := (Finset.union_eq_empty.mp both).1
  have fused : ∀ (r : Wiring signature a b) (s : Wiring signature b c), (seqFusion r s).support = ∅ := fun _ _ => rfl
  simp only [pasted, PresentedCell.support, (normalizeSeq p q).property,
    WirePass.witness_support, Circuit.needs, wireTrack_support, inner, fused,
    RewriteTrack.support, Finset.union_empty]

/-- The residual is the previously defined canonical fusion followed by the
actual seqNormal derivation; it never undoes fusion or reintroduces the source. -/
def square {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    { cell : Cell
      (.comp (.step (seqFusion p q))
        (WirePass.witness (original := Structural.Fusion.rules) (.wire (Wire.seq p q))))
      (.comp (WirePass.witness (original := Structural.Fusion.rules) (.seq (.wire p) (.wire q)))
        (WireFusionResidual.seqResidual p q)) // PresentedCell.support cell = ∅ } := by
  let family (path : RewriteTrack (relators := UnionRules)
      (.wire (Wire.seq p q)) (WirePass.output (.wire (Wire.seq p q)))) :=
    { cell : Cell (.comp (.step (seqFusion p q)) path)
      (.comp (WirePass.witness (original := Structural.Fusion.rules) (.seq (.wire p) (.wire q)))
        (WireFusionResidual.seqResidual p q)) // PresentedCell.support cell = ∅ }
  exact cast (congrArg family (seq_normalization_track p q)) ⟨pasted p q, pasted_support p q⟩

theorem context_support {a b c x y} (p : Wiring signature a b) (q : Wiring signature b c)
    (place : Placement (signature := signature) a c x y) :
    PresentedCell.support ((square p q).val.whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, (square p q).property, Finset.empty_union]

theorem context_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c x y} (p : Wiring signature a b) (q : Wiring signature b c)
    (place : Placement (signature := signature) a c x y) (changed : Finset Nat)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : PMF (Context × (State × Bundle Value x))) :
    ∃ left : Holds updated (place.apply (.seq (.wire p) (.wire q))).needs,
    ∃ right : Holds updated (place.apply (WirePass.output (.wire (Wire.seq p q)))).needs,
      law.bind (fun past =>
        (Stateful.evaluate model.base (place.apply (.seq (.wire p) (.wire q))) left past.2.1 past.2.2).map
          (fun next => (past, next))) =
      law.bind (fun past =>
        (Stateful.evaluate model.base (place.apply (WirePass.output (.wire (Wire.seq p q)))) right past.2.1 past.2.2).map
          (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support ((square p q).val.whisker place)) := by
    rw [context_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support ((square p q).val.whisker place)) changed) := by
    rw [context_support]; exact rechecked
  exact Stateful.cell_repaired_joint (checked model) ((square p q).val.whisker place)
    changed cached' unchanged rechecked' law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.SequentialFusionWirePass
