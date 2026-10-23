import Foundation.Examples.MixedCircuitUnifiedFusionResolution
import Foundation.Logic.Polygraph.FourNaturality

/-! Internal wire contexts are related to mixed placements by the actual
wire-fusion edges. Naturality for a whole cartesian track is generated from
single-step fusion squares and Four groupoid operations, not a new root. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFrame
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Overlap
set_option backward.isDefEq.respectTransparency false

inductive Frame : Port signature → Port signature → Port signature → Port signature → Type where
  | seqLeft {a b c} (fixed : Wiring signature b c) : Frame a b a c
  | seqRight {a b c} (fixed : Wiring signature a b) : Frame b c a c
  | tensorLeft {a b c d} (fixed : Wiring signature c d) : Frame a b (.pair a c) (.pair b d)
  | tensorRight {a b c d} (fixed : Wiring signature a b) : Frame c d (.pair a c) (.pair b d)

def Frame.apply : {a b c d : Port signature} → Frame a b c d → Wiring signature a b → Wiring signature c d
  | _, _, _, _, .seqLeft fixed, wire => .seq wire fixed
  | _, _, _, _, .seqRight fixed, wire => .seq fixed wire
  | _, _, _, _, .tensorLeft fixed, wire => .tensor wire fixed
  | _, _, _, _, .tensorRight fixed, wire => .tensor fixed wire

def Frame.place : {a b c d : Port signature} → Frame a b c d → Placement (signature := signature) a b c d
  | _, _, _, _, .seqLeft fixed => .seqLeft (.wire fixed)
  | _, _, _, _, .seqRight fixed => .seqRight (.wire fixed)
  | _, _, _, _, .tensorLeft fixed => .tensorLeft (.wire fixed)
  | _, _, _, _, .tensorRight fixed => .tensorRight (.wire fixed)

def Frame.cartStep : {a b c d : Port signature} → (frame : Frame a b c d) → {p q : Wiring signature a b} →
    Cartesian.Step p q → Cartesian.Step (frame.apply p) (frame.apply q)
  | _, _, _, _, .seqLeft fixed, _, _, change => .seqLeft change fixed
  | _, _, _, _, .seqRight fixed, _, _, change => .seqRight fixed change
  | _, _, _, _, .tensorLeft fixed, _, _, change => .tensorLeft change fixed
  | _, _, _, _, .tensorRight fixed, _, _, change => .tensorRight fixed change

def Frame.oldStep : {a b c d : Port signature} → (frame : Frame a b c d) → {p q : Wiring signature a b} →
    Structural.WireEdit p q → Structural.WireEdit (frame.apply p) (frame.apply q)
  | _, _, _, _, .seqLeft fixed, _, _, change => .seqLeft change fixed
  | _, _, _, _, .seqRight fixed, _, _, change => .seqRight fixed change
  | _, _, _, _, .tensorLeft fixed, _, _, change => .tensorLeft change fixed
  | _, _, _, _, .tensorRight fixed, _, _, change => .tensorRight fixed change

def Frame.cartTrack {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    Cartesian.ProofTrack (frame.apply p) (frame.apply q) := path.map frame.apply (fun change => frame.cartStep change)

def Frame.fusion : {a b c d : Port signature} → (frame : Frame a b c d) → (wire : Wiring signature a b) →
    Step UnionRules (frame.place.apply (.wire wire)) (.wire (frame.apply wire))
  | _, _, _, _, .seqLeft fixed, wire => seqFusion wire fixed
  | _, _, _, _, .seqRight fixed, wire => seqFusion fixed wire
  | _, _, _, _, .tensorLeft fixed, wire => tensorFusion wire fixed
  | _, _, _, _, .tensorRight fixed, wire => tensorFusion fixed wire

def Frame.oldNaturality {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    Cell (.comp (frame.place.track (.step (oldEdit change))) (.step (frame.fusion q)))
      (.comp (.step (frame.fusion p)) (.step (oldEdit (frame.oldStep change)))) := by
  cases frame with
  | seqLeft fixed => exact oldSeqLeft change fixed
  | seqRight fixed => exact oldSeqRight fixed change
  | tensorLeft fixed => exact oldTensorLeft change fixed
  | tensorRight fixed => exact oldTensorRight fixed change

def Frame.cartStepNaturality {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b} (change : Cartesian.Step p q) :
    Cell (.comp (frame.place.track (.step (edit change))) (.step (frame.fusion q)))
      (.comp (.step (frame.fusion p)) (.step (edit (frame.cartStep change)))) := by
  cases frame with
  | seqLeft fixed => exact (LocalDiagram.seqLeft change fixed).cell
  | seqRight fixed => exact (LocalDiagram.seqRight fixed change).cell
  | tensorLeft fixed => exact (LocalDiagram.tensorLeft change fixed).cell
  | tensorRight fixed => exact (LocalDiagram.tensorRight fixed change).cell

def Frame.cartNaturality {a b c d} (frame : Frame a b c d) : {p q : Wiring signature a b} →
    (path : Cartesian.ProofTrack p q) →
    Cell (.comp (frame.place.track (Stateful.WiringUnion.wireTrack path)) (.step (frame.fusion q)))
      (.comp (.step (frame.fusion p)) (Stateful.WiringUnion.wireTrack (frame.cartTrack path)))
  | p, _, .refl _ => (Four.leftUnit (.step (frame.fusion p))).trans (Four.rightUnit (.step (frame.fusion p))).symm
  | _, _, .step change => frame.cartStepNaturality change
  | p, r, .comp (b := q) first second =>
      (Four.assoc (frame.place.track (Stateful.WiringUnion.wireTrack first))
        (frame.place.track (Stateful.WiringUnion.wireTrack second)) (.step (frame.fusion r))).trans
      ((Four.comp (.refl _) (frame.cartNaturality second)).trans
        ((Four.assoc (frame.place.track (Stateful.WiringUnion.wireTrack first)) (.step (frame.fusion q))
          (Stateful.WiringUnion.wireTrack (frame.cartTrack second))).symm.trans
          ((Four.comp (frame.cartNaturality first) (.refl _)).trans
            (Four.assoc (.step (frame.fusion p)) (Stateful.WiringUnion.wireTrack (frame.cartTrack first))
              (Stateful.WiringUnion.wireTrack (frame.cartTrack second))))))
  | p, q, .inv child =>
      FourNaturality.invertSquare (frame.place.track (Stateful.WiringUnion.wireTrack child))
        (.step (frame.fusion p)) (.step (frame.fusion q))
        (Stateful.WiringUnion.wireTrack (frame.cartTrack child)) (frame.cartNaturality child)

theorem Frame.place_needs {a b c d} (frame : Frame a b c d) : frame.place.needs = ∅ := by cases frame <;> rfl

theorem Frame.fusion_support {a b c d} (frame : Frame a b c d) (wire : Wiring signature a b) :
    (frame.fusion wire).support = ∅ := by
  cases frame <;> simp [Frame.fusion, seqFusion, tensorFusion, Stateful.WiringUnion.embedStep,
    Step.support, Primitive.support, Relator.support, UnionRules, Stateful.WiringUnion.rules,
    Structural.Fusion.rules, Structural.rules, Circuit.needs]

theorem Frame.compiled_support {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (path : Cartesian.ProofTrack p q) :
    RewriteTrack.support (frame.place.track (Stateful.WiringUnion.wireTrack (original := Structural.Fusion.rules) path)) = ∅ := by
  rw [Placement.track_support, Stateful.WiringUnion.wireTrack_support, Frame.place_needs, Finset.union_empty]

theorem Frame.oldNaturality_support {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (change : Structural.WireEdit p q) : PresentedCell.support (frame.oldNaturality change) = ∅ := by
  cases frame with
  | seqLeft fixed => exact oldSeqLeft_support change fixed
  | seqRight fixed => exact oldSeqRight_support fixed change
  | tensorLeft fixed => exact oldTensorLeft_support change fixed
  | tensorRight fixed => exact oldTensorRight_support fixed change

theorem Frame.cartStepNaturality_support {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (change : Cartesian.Step p q) : PresentedCell.support (frame.cartStepNaturality change) = ∅ := by
  cases frame with
  | seqLeft fixed => exact local_cell_support (LocalDiagram.seqLeft change fixed)
  | seqRight fixed => exact local_cell_support (LocalDiagram.seqRight fixed change)
  | tensorLeft fixed => exact local_cell_support (LocalDiagram.tensorLeft change fixed)
  | tensorRight fixed => exact local_cell_support (LocalDiagram.tensorRight fixed change)

theorem Frame.cartNaturality_support {a b c d} (frame : Frame a b c d) {p q : Wiring signature a b}
    (path : Cartesian.ProofTrack p q) : PresentedCell.support (frame.cartNaturality path) = ∅ := by
  induction path with
  | refl => simp only [Frame.cartNaturality, PresentedCell.support, RewriteTrack.support, Frame.fusion_support, Finset.union_empty]
  | step change => exact Frame.cartStepNaturality_support frame change
  | comp first second one two =>
      simp only [Frame.cartNaturality, PresentedCell.support, RewriteTrack.support,
        Frame.compiled_support, Stateful.WiringUnion.wireTrack_support, Frame.fusion_support, one, two, Finset.union_empty]
  | inv child ih =>
      simp only [Frame.cartNaturality, FourNaturality.invertSquare, FourNaturality.cancelPrefix,
        FourNaturality.undoLeft, FourNaturality.undoInversePrefix, FourNaturality.undoRight,
        PresentedCell.support, RewriteTrack.support, Frame.compiled_support,
        Stateful.WiringUnion.wireTrack_support, Frame.fusion_support, ih, Finset.union_empty]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFrame
