import Foundation.Examples.MixedCircuitStatefulWiringHigher
import Foundation.Crypto.Logic.Polygraph.MixedCircuitWireNormalization

/-! Actual path-valued residuals for sequential/tensor fusion after the wire
pass. The old fusion root is followed by an expanded eighteen-law derivation.
The higher normalization/fusion square remains a separate obligation. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFusionResidual
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Stateful.WiringUnion
open WirePass
set_option backward.isDefEq.respectTransparency false

def canonical {a b} (p : Wiring signature a b) := Cartesian.reify (TypedRouting.normal p)

def seqWire {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    Cartesian.Cell (.seq (canonical p) (canonical q)) (canonical (.seq p q)) := by
  have layout : Cartesian.substitute (TypedRouting.normal p) (TypedRouting.normal q) = TypedRouting.normal (.seq p q) := by
    have same := Cartesian.normalize_layout (Wire.seq p q)
    change Cartesian.substitute (Cartesian.normalize p).layout (Cartesian.normalize q).layout = _ at same
    simpa only [Cartesian.normalize_layout] using same
  let family (routing : TypedRouting.Layout a c) :=
    Cartesian.Cell (Wire.seq (canonical p) (canonical q)) (Cartesian.reify routing)
  exact cast (congrArg family layout) (Cartesian.seqNormal (TypedRouting.normal p) (TypedRouting.normal q))

def tensorWire {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    Cartesian.Cell (.tensor (canonical p) (canonical q)) (canonical (.tensor p q)) := by
  have layout : TypedRouting.normal (Wire.tensor (canonical p) (canonical q)) = TypedRouting.normal (Wire.tensor p q) := by
    apply (TypedRouting.normal_complete _ _).mpr
    intro family value
    exact congrArg₂ Prod.mk ((Cartesian.normalizeCell p).sound family value.1).symm
      ((Cartesian.normalizeCell q).sound family value.2).symm
  let family (routing : TypedRouting.Layout (.pair a c) (.pair b d)) :=
    Cartesian.Cell (Wire.tensor (canonical p) (canonical q)) (Cartesian.reify routing)
  exact cast (congrArg family layout) (Cartesian.normalizeCell (Wire.tensor (canonical p) (canonical q)))

def seqResidual {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    RewriteTrack (relators := UnionRules) (output (.seq (.wire p) (.wire q))) (output (.wire (.seq p q))) :=
  .comp (.step (seqFusion (canonical p) (canonical q)))
    (wireTrack (original := Structural.Fusion.rules) (seqWire p q).toTrack)

def tensorResidual {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    RewriteTrack (relators := UnionRules) (output (.tensor (.wire p) (.wire q))) (output (.wire (.tensor p q))) :=
  .comp (.step (tensorFusion (canonical p) (canonical q)))
    (wireTrack (original := Structural.Fusion.rules) (tensorWire p q).toTrack)

theorem seqResidual_support {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    RewriteTrack.support (seqResidual p q) = ∅ := by
  have fused : (seqFusion (canonical p) (canonical q)).support = ∅ := rfl
  simp only [seqResidual, RewriteTrack.support, wireTrack_support, fused, Finset.union_empty]

theorem tensorResidual_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    RewriteTrack.support (tensorResidual p q) = ∅ := by
  have fused : (tensorFusion (canonical p) (canonical q)).support = ∅ := rfl
  simp only [tensorResidual, RewriteTrack.support, wireTrack_support, fused, Finset.union_empty]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.WireFusionResidual
