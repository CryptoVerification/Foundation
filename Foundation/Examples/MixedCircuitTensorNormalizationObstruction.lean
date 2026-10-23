import Foundation.Examples.MixedCircuitWireFusionTrackNaturality
import Foundation.Logic.Polygraph.StructuralCartesianCoherenceInvariant

/-! A concrete obligation for canonical tensor fusion: component-first and
direct normalization paths are not comparable in the OLD partial pure basis.
No non-derivability claim for the richer mixed/unit-critical basis is made. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.TensorNormalizationObstruction
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
set_option backward.isDefEq.respectTransparency false

def firstWire : Wiring signature (.pair MAC.finish MAC.finish) (.pair MAC.finish MAC.finish) := .identity _
def secondWire : Wiring signature MAC.finish MAC.finish := .identity _

def componentPath := (Cartesian.Cell.tensor (Cartesian.normalizeCell firstWire)
  (Cartesian.normalizeCell secondWire)).toTrack

def componentThenCanonical := Track.comp componentPath (WireFusionResidual.tensorWire firstWire secondWire).toTrack

def direct := (Cartesian.normalizeCell (Wire.tensor firstWire secondWire)).toTrack

theorem component_weight :
    @Eq ((Int × Int) × Int) (Cartesian.Higher.CoherenceInvariant.trackWeight componentThenCanonical) ((4, 4), 0) := by
  rfl

theorem direct_weight : @Eq ((Int × Int) × Int) (Cartesian.Higher.CoherenceInvariant.trackWeight direct) ((2, 2), 0) := by
  rfl

theorem not_comparable : ¬ Nonempty (Cartesian.Higher.Homotopy componentThenCanonical direct) := by
  rintro ⟨cell⟩
  have same := Cartesian.Higher.CoherenceInvariant.homotopy_weight cell
  rw [component_weight, direct_weight] at same
  have impossible : (4 : Int) = 2 := congrArg (fun value : (Int × Int) × Int => value.1.1) same
  omega

theorem component_path_realizes :
    Stateful.WiringUnion.wireTrack (original := Structural.Fusion.rules) componentPath =
      WireFusionTrackNaturality.tensorInner (Cartesian.normalizeCell firstWire).toTrack
        (Cartesian.normalizeCell secondWire).toTrack := by
  simp only [componentPath, Cartesian.Cell.toTrack, Cartesian.tensorLeftTrack, Cartesian.tensorRightTrack,
    Stateful.WiringUnion.wireTrack, Track.map, FourNaturality.map_map,
    WireFusionTrackNaturality.tensorInner, edit]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.TensorNormalizationObstruction
