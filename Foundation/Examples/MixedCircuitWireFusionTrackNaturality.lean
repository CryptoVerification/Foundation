import Foundation.Examples.MixedCircuitWireFusionResidual
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedPathNaturality

/-! Extend the four existing local wire/fusion squares to arbitrary actual
eighteen-law tracks, including formal inverses. This does not assert pure-wire
higher coherence or identify different chosen normalization proofs. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFusionTrackNaturality
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
set_option backward.isDefEq.respectTransparency false

private theorem mapped_empty {A : Type} {R : A → A → Type}
    {a b : Port signature} (f : A → Circuit signature a b)
    (edge : ∀ {p q}, R p q → Step UnionRules (f p) (f q))
    (nodes : ∀ p, (f p).needs = ∅) (edges : ∀ {p q} (e : R p q), (edge e).support = ∅)
    {p q} (path : Track R p q) : RewriteTrack.support (path.map f edge) = ∅ := by
  induction path <;> simp_all only [Track.map, RewriteTrack.support, Finset.union_empty]

private theorem natural_empty {A : Type} {R : A → A → Type}
    {a b : Port signature} (f g : A → Circuit signature a b)
    (mapF : ∀ {p q}, R p q → Step UnionRules (f p) (f q))
    (mapG : ∀ {p q}, R p q → Step UnionRules (g p) (g q))
    (component : ∀ p, RewriteTrack (relators := UnionRules) (f p) (g p))
    (square : ∀ {p q} (e : R p q),
      Cell (.comp (.step (mapF e)) (component q)) (.comp (component p) (.step (mapG e))))
    (fNodes : ∀ p, (f p).needs = ∅) (gNodes : ∀ p, (g p).needs = ∅)
    (fEdges : ∀ {p q} (e : R p q), (mapF e).support = ∅)
    (gEdges : ∀ {p q} (e : R p q), (mapG e).support = ∅)
    (components : ∀ p, (component p).support = ∅)
    (squares : ∀ {p q} (e : R p q), PresentedCell.support (square e) = ∅)
    {p q} (path : Track R p q) :
    PresentedCell.support (basis := basis)
      (FourNaturality.natural f g mapF mapG component square path) = ∅ := by
  induction path with
  | refl p => simp only [FourNaturality.natural, PresentedCell.support, components, Finset.union_empty]
  | step e => exact squares e
  | comp one two ih₁ ih₂ =>
      simp only [FourNaturality.natural, PresentedCell.support,
        mapped_empty f mapF fNodes fEdges, mapped_empty g mapG gNodes gEdges,
        components, ih₁, ih₂, Finset.union_empty]
  | inv child ih =>
      exact (PresentedPathNaturality.invertSquare_support _ _ _ _ _).trans ih

def seqLeft {a b c} {p p' : Wiring signature a b}
    (path : Cartesian.ProofTrack p p') (q : Wiring signature b c) :
    Cell
      (.comp (path.map (fun w => Circuit.seq (.wire w) (.wire q))
        (fun change => .seqLeft (edit change) (.wire q))) (.step (seqFusion p' q)))
      (.comp (.step (seqFusion p q))
        (path.map (fun w => Circuit.wire (Wire.seq w q))
          (fun change => edit (.seqLeft change q)))) :=
  FourNaturality.natural _ _ _ _ (fun w => .step (seqFusion w q))
    (fun change => (LocalDiagram.seqLeft change q).cell) path

def seqRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c}
    (path : Cartesian.ProofTrack q q') :
    Cell
      (.comp (path.map (fun w => Circuit.seq (.wire p) (.wire w))
        (fun change => .seqRight (.wire p) (edit change))) (.step (seqFusion p q')))
      (.comp (.step (seqFusion p q))
        (path.map (fun w => Circuit.wire (Wire.seq p w))
          (fun change => edit (.seqRight p change)))) :=
  FourNaturality.natural _ _ _ _ (fun w => .step (seqFusion p w))
    (fun change => (LocalDiagram.seqRight p change).cell) path

def tensorLeft {a b c d} {p p' : Wiring signature a b}
    (path : Cartesian.ProofTrack p p') (q : Wiring signature c d) :
    Cell
      (.comp (path.map (fun w => Circuit.tensor (.wire w) (.wire q))
        (fun change => .tensorLeft (edit change) (.wire q))) (.step (tensorFusion p' q)))
      (.comp (.step (tensorFusion p q))
        (path.map (fun w => Circuit.wire (Wire.tensor w q))
          (fun change => edit (.tensorLeft change q)))) :=
  FourNaturality.natural _ _ _ _ (fun w => .step (tensorFusion w q))
    (fun change => (LocalDiagram.tensorLeft change q).cell) path

def tensorRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d}
    (path : Cartesian.ProofTrack q q') :
    Cell
      (.comp (path.map (fun w => Circuit.tensor (.wire p) (.wire w))
        (fun change => .tensorRight (.wire p) (edit change))) (.step (tensorFusion p q')))
      (.comp (.step (tensorFusion p q))
        (path.map (fun w => Circuit.wire (Wire.tensor p w))
          (fun change => edit (.tensorRight p change)))) :=
  FourNaturality.natural _ _ _ _ (fun w => .step (tensorFusion p w))
    (fun change => (LocalDiagram.tensorRight p change).cell) path

theorem seqLeft_support {a b c} {p p' : Wiring signature a b}
    (path : Cartesian.ProofTrack p p') (q : Wiring signature b c) :
    PresentedCell.support (seqLeft path q) = ∅ := by
  apply natural_empty
  all_goals first | intro w; rfl | intro x y change; rfl

theorem seqRight_support {a b c} (p : Wiring signature a b)
    {q q' : Wiring signature b c} (path : Cartesian.ProofTrack q q') :
    PresentedCell.support (seqRight p path) = ∅ := by
  apply natural_empty
  all_goals first | intro w; rfl | intro x y change; rfl

theorem tensorLeft_support {a b c d} {p p' : Wiring signature a b}
    (path : Cartesian.ProofTrack p p') (q : Wiring signature c d) :
    PresentedCell.support (tensorLeft path q) = ∅ := by
  apply natural_empty
  all_goals first | intro w; rfl | intro x y change; rfl

theorem tensorRight_support {a b c d} (p : Wiring signature a b)
    {q q' : Wiring signature c d} (path : Cartesian.ProofTrack q q') :
    PresentedCell.support (tensorRight p path) = ∅ := by
  apply natural_empty
  all_goals first | intro w; rfl | intro x y change; rfl

def seqOuter {a b c} {p p' : Wiring signature a b} {q q' : Wiring signature b c}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :=
  Track.comp
    (one.map (fun w => Circuit.seq (.wire w) (.wire q)) (fun e => Step.seqLeft (edit e) (.wire q)))
    (two.map (fun w => Circuit.seq (.wire p') (.wire w)) (fun e => Step.seqRight (.wire p') (edit e)))

def seqInner {a b c} {p p' : Wiring signature a b} {q q' : Wiring signature b c}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :=
  Track.comp
    (one.map (fun w => Circuit.wire (Wire.seq w q)) (fun e => edit (.seqLeft e q)))
    (two.map (fun w => Circuit.wire (Wire.seq p' w)) (fun e => edit (.seqRight p' e)))

def seqPair {a b c} {p p' : Wiring signature a b} {q q' : Wiring signature b c}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :
    Cell (.comp (seqOuter one two) (.step (seqFusion p' q')))
      (.comp (.step (seqFusion p q)) (seqInner one two)) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (seqRight p' two)).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (seqLeft one q) (.refl _)).trans (Four.assoc _ _ _))))

theorem seqPair_support {a b c} {p p' : Wiring signature a b} {q q' : Wiring signature b c}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :
    PresentedCell.support (seqPair one two) = ∅ := by
  have h0 := mapped_empty (fun (w : Wiring signature a b) => Circuit.seq (.wire w) (.wire q)) (fun e => Step.seqLeft (edit e) (.wire q))
    (fun _ => rfl) (by intros; rfl) one
  have h1 := mapped_empty (fun (w : Wiring signature b c) => Circuit.seq (.wire p') (.wire w)) (fun e => Step.seqRight (.wire p') (edit e))
    (fun _ => rfl) (by intros; rfl) two
  have h2 := mapped_empty (fun (w : Wiring signature a b) => Circuit.wire (Wire.seq w q)) (fun e => edit (.seqLeft e q))
    (fun _ => rfl) (by intros; rfl) one
  have h3 := mapped_empty (fun (w : Wiring signature b c) => Circuit.wire (Wire.seq p' w)) (fun e => edit (.seqRight p' e))
    (fun _ => rfl) (by intros; rfl) two
  have fusionSupport : ∀ (r : Wiring signature a b) (t : Wiring signature b c),
      (seqFusion r t).support = ∅ := fun _ _ => rfl
  simp only [seqPair, PresentedCell.support, seqLeft_support, seqRight_support,
    h0, h1, h2, h3, fusionSupport, RewriteTrack.support, Finset.union_empty]

def tensorOuter {a b c d} {p p' : Wiring signature a b} {q q' : Wiring signature c d}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :=
  Track.comp
    (one.map (fun w => Circuit.tensor (.wire w) (.wire q)) (fun e => Step.tensorLeft (edit e) (.wire q)))
    (two.map (fun w => Circuit.tensor (.wire p') (.wire w)) (fun e => Step.tensorRight (.wire p') (edit e)))

def tensorInner {a b c d} {p p' : Wiring signature a b} {q q' : Wiring signature c d}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :=
  Track.comp
    (one.map (fun w => Circuit.wire (Wire.tensor w q)) (fun e => edit (.tensorLeft e q)))
    (two.map (fun w => Circuit.wire (Wire.tensor p' w)) (fun e => edit (.tensorRight p' e)))

def tensorPair {a b c d} {p p' : Wiring signature a b} {q q' : Wiring signature c d}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :
    Cell (.comp (tensorOuter one two) (.step (tensorFusion p' q')))
      (.comp (.step (tensorFusion p q)) (tensorInner one two)) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (tensorRight p' two)).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (tensorLeft one q) (.refl _)).trans (Four.assoc _ _ _))))

theorem tensorPair_support {a b c d} {p p' : Wiring signature a b} {q q' : Wiring signature c d}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q') :
    PresentedCell.support (tensorPair one two) = ∅ := by
  have h0 := mapped_empty (fun (w : Wiring signature a b) => Circuit.tensor (.wire w) (.wire q)) (fun e => Step.tensorLeft (edit e) (.wire q))
    (fun _ => rfl) (by intros; rfl) one
  have h1 := mapped_empty (fun (w : Wiring signature c d) => Circuit.tensor (.wire p') (.wire w)) (fun e => Step.tensorRight (.wire p') (edit e))
    (fun _ => rfl) (by intros; rfl) two
  have h2 := mapped_empty (fun (w : Wiring signature a b) => Circuit.wire (Wire.tensor w q)) (fun e => edit (.tensorLeft e q))
    (fun _ => rfl) (by intros; rfl) one
  have h3 := mapped_empty (fun (w : Wiring signature c d) => Circuit.wire (Wire.tensor p' w)) (fun e => edit (.tensorRight p' e))
    (fun _ => rfl) (by intros; rfl) two
  have fusionSupport : ∀ (r : Wiring signature a b) (t : Wiring signature c d),
      (tensorFusion r t).support = ∅ := fun _ _ => rfl
  simp only [tensorPair, PresentedCell.support, tensorLeft_support, tensorRight_support,
    h0, h1, h2, h3, fusionSupport, RewriteTrack.support, Finset.union_empty]

theorem seqOuter_normalize {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    seqOuter (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack =
      WirePass.witness (original := Structural.Fusion.rules) (.seq (.wire p) (.wire q)) := by
  simp only [seqOuter, WirePass.witness, WirePass.output, Stateful.WiringUnion.normalize, Placement.track,
    wireTrack, FourNaturality.map_map, Placement.apply, Placement.step, edit]

theorem tensorOuter_normalize {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    tensorOuter (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack =
      WirePass.witness (original := Structural.Fusion.rules) (.tensor (.wire p) (.wire q)) := by
  simp only [tensorOuter, WirePass.witness, WirePass.output, Stateful.WiringUnion.normalize, Placement.track,
    wireTrack, FourNaturality.map_map, Placement.apply, Placement.step, edit]

def normalizeSeq {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    { cell : Cell
      (.comp (WirePass.witness (original := Structural.Fusion.rules) (.seq (.wire p) (.wire q)))
        (.step (seqFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (seqFusion p q))
        (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ } := by
  have result := (show { cell : Cell
      (.comp (seqOuter (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)
        (.step (seqFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (seqFusion p q))
        (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ } from
    ⟨seqPair _ _, seqPair_support _ _⟩)
  let family (outer : RewriteTrack (relators := UnionRules)
      (Circuit.seq (.wire p) (.wire q)) (WirePass.output (Circuit.seq (.wire p) (.wire q)))) :=
    { cell : Cell (.comp outer (.step (seqFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (seqFusion p q))
        (seqInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ }
  exact cast (congrArg family (seqOuter_normalize p q)) result

def normalizeTensor {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    { cell : Cell
      (.comp (WirePass.witness (original := Structural.Fusion.rules) (.tensor (.wire p) (.wire q)))
        (.step (tensorFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (tensorFusion p q))
        (tensorInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ } := by
  have result := (show { cell : Cell
      (.comp (tensorOuter (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)
        (.step (tensorFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (tensorFusion p q))
        (tensorInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ } from
    ⟨tensorPair _ _, tensorPair_support _ _⟩)
  let family (outer : RewriteTrack (relators := UnionRules)
      (Circuit.tensor (.wire p) (.wire q)) (WirePass.output (Circuit.tensor (.wire p) (.wire q)))) :=
    { cell : Cell (.comp outer (.step (tensorFusion (WireFusionResidual.canonical p) (WireFusionResidual.canonical q))))
      (.comp (.step (tensorFusion p q))
        (tensorInner (Cartesian.normalizeCell p).toTrack (Cartesian.normalizeCell q).toTrack)) //
      PresentedCell.support cell = ∅ }
  exact cast (congrArg family (tensorOuter_normalize p q)) result

theorem seqPair_context_support {a b c x y} {p p' : Wiring signature a b} {q q' : Wiring signature b c}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q')
    (place : Placement (signature := signature) a c x y) :
    PresentedCell.support ((seqPair one two).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, seqPair_support, Finset.empty_union]

theorem tensorPair_context_support {a b c d x y} {p p' : Wiring signature a b} {q q' : Wiring signature c d}
    (one : Cartesian.ProofTrack p p') (two : Cartesian.ProofTrack q q')
    (place : Placement (signature := signature) (.pair a c) (.pair b d) x y) :
    PresentedCell.support ((tensorPair one two).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, tensorPair_support, Finset.empty_union]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFusionTrackNaturality
