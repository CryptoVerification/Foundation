import Foundation.Logic.Polygraph.StructuralCartesianProjectedTrackNaturality
import Foundation.Logic.Polygraph.StructuralCartesianExpansionCritical

/-! Projection of eta assembly agrees with the supplied component path.
Specializing to the ACTUAL identityNormal definition yields its two product
projection compatibility squares. No normalizer or comparison is postulated. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.ProjectionCoherence
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def productLift {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : ProductCritical.Cell first second) : Cell first second := embed (DistributionCritical.embed cell)

def inverseEtaFst {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    Cell (.comp (.inv (ProductCritical.etaFst p)) (ProductCritical.betaEtaFst p)) (.refl _) :=
  (Four.comp (Four.inverse (productLift (ProductCritical.fstCell p))) (.refl _)).trans (Four.leftInv _)

def inverseEtaSnd {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    Cell (.comp (.inv (ProductCritical.etaSnd p)) (ProductCritical.betaEtaSnd p)) (.refl _) :=
  (Four.comp (Four.inverse (productLift (ProductCritical.sndCell p))) (.refl _)).trans (Four.leftInv _)

def assemble {a b c : Shape Atom} (p : Wire a (.pair b c)) {left : Wire a b} {right : Wire a c}
    (first : ProofTrack (.seq p (fst b c)) left) (second : ProofTrack (.seq p (snd b c)) right) :=
  Track.comp (.inv (Track.step (Step.root (.eta p)))) (ProjectedTrackNaturality.forkPaths first second)

def assembledFst {a b c : Shape Atom} (p : Wire a (.pair b c)) {left : Wire a b} {right : Wire a c}
    (first : ProofTrack (.seq p (fst b c)) left) (second : ProofTrack (.seq p (snd b c)) right) :
    Cell (.comp (ProductTracks.firstProjection (assemble p first second)) (.step (.root (.betaFst left right)))) first :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (oldLift (ProjectedTrackNaturality.fstBoth first second))).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (inverseEtaFst p) (.refl _)).trans (Four.leftUnit first))))

def assembledSnd {a b c : Shape Atom} (p : Wire a (.pair b c)) {left : Wire a b} {right : Wire a c}
    (first : ProofTrack (.seq p (fst b c)) left) (second : ProofTrack (.seq p (snd b c)) right) :
    Cell (.comp (ProductTracks.secondProjection (assemble p first second)) (.step (.root (.betaSnd left right)))) second :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (oldLift (ProjectedTrackNaturality.sndBoth first second))).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (inverseEtaSnd p) (.refl _)).trans (Four.leftUnit second))))

def leftCanonical (a b : Shape Atom) : Wire (.pair a b) a := reify (a.map (fun _ => TypedRouting.Slot.left) (TypedRouting.universal a))
def rightCanonical (a b : Shape Atom) : Wire (.pair a b) b := reify (b.map (fun _ => TypedRouting.Slot.right) (TypedRouting.universal b))

def leftIdentityProjection (a b : Shape Atom) :=
  ((Cartesian.Cell.root (.leftId (fst a b))).trans (projectLeft a b (identityNormal a))).toTrack

def rightIdentityProjection (a b : Shape Atom) :=
  ((Cartesian.Cell.root (.leftId (snd a b))).trans (projectRight a b (identityNormal b))).toTrack

def identityPairAssembly (a b : Shape Atom) :
    Cell (identityNormal (.pair a b)).toTrack
      (assemble (Wire.identity (.pair a b)) (leftIdentityProjection a b) (rightIdentityProjection a b)) := by
  change Cell (.comp (.inv (.step (.root (.eta (.identity (.pair a b))))))
    (.comp (.refl _) (ProjectedTrackNaturality.forkPaths (leftIdentityProjection a b) (rightIdentityProjection a b)))) _
  exact Four.comp (.refl _) (Four.leftUnit _)

def identityNormalFst (a b : Shape Atom) :
    Cell (.comp (ProductTracks.firstProjection (identityNormal (.pair a b)).toTrack)
      (.step (.root (.betaFst (leftCanonical a b) (rightCanonical a b))))) (leftIdentityProjection a b) :=
  (Four.comp (whisker (.seqLeft (fst a b)) (identityPairAssembly a b)) (.refl _)).trans
    (assembledFst (Wire.identity (.pair a b)) (leftIdentityProjection a b) (rightIdentityProjection a b))

def identityNormalSnd (a b : Shape Atom) :
    Cell (.comp (ProductTracks.secondProjection (identityNormal (.pair a b)).toTrack)
      (.step (.root (.betaSnd (leftCanonical a b) (rightCanonical a b))))) (rightIdentityProjection a b) :=
  (Four.comp (whisker (.seqLeft (snd a b)) (identityPairAssembly a b)) (.refl _)).trans
    (assembledSnd (Wire.identity (.pair a b)) (leftIdentityProjection a b) (rightIdentityProjection a b))

/-- The public normalizer's endpoint transport is definitionally trivial for identity. -/
theorem normalizeIdentity (a : Shape Atom) : normalizeCell (Wire.identity a) = identityNormal a := by
  rfl

def normalizeIdentityFst (a b : Shape Atom) :
    Cell (.comp (ProductTracks.firstProjection (normalizeCell (Wire.identity (.pair a b))).toTrack)
      (.step (.root (.betaFst (leftCanonical a b) (rightCanonical a b))))) (leftIdentityProjection a b) := by
  rw [normalizeIdentity]
  exact identityNormalFst a b

def normalizeIdentitySnd (a b : Shape Atom) :
    Cell (.comp (ProductTracks.secondProjection (normalizeCell (Wire.identity (.pair a b))).toTrack)
      (.step (.root (.betaSnd (leftCanonical a b) (rightCanonical a b))))) (rightIdentityProjection a b) := by
  rw [normalizeIdentity]
  exact identityNormalSnd a b

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.ProjectionCoherence
