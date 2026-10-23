import Foundation.Logic.Polygraph.StructuralCartesianTensorProjectionPeak
/-! Explicit two-versus-three forward paths for unit expansion versus copy/projection.
No higher comparison is assumed here. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionUnitPeak
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def rightExpanded (a : Shape Atom) :=
  Track.comp (Track.step (Step.seqRight (fork (.identity a) (.discard a)) (.root (.rightUnitExpand a))))
    (Track.step (Step.root (.betaFst (.identity a) (.discard a))))

def rightCopied (a : Shape Atom) :=
  Track.comp (Track.step (Step.root (.assoc (.copy a) (.tensor (.identity a) (.discard a)) (.rightUnit a)))) <|
  Track.comp (Track.step (Step.seqLeft (.root (.copyExpand a)) (fst a a))) <|
  Track.step (Step.root (.betaFst (.identity a) (.identity a)))

def leftExpanded (a : Shape Atom) :=
  Track.comp (Track.step (Step.seqRight (fork (.discard a) (.identity a)) (.root (.leftUnitExpand a))))
    (Track.step (Step.root (.betaSnd (.discard a) (.identity a))))

def leftCopied (a : Shape Atom) :=
  Track.comp (Track.step (Step.root (.assoc (.copy a) (.tensor (.discard a) (.identity a)) (.leftUnit a)))) <|
  Track.comp (Track.step (Step.seqLeft (.root (.copyExpand a)) (snd a a))) <|
  Track.step (Step.root (.betaSnd (.identity a) (.identity a)))

theorem right_scalar_iff (name : Atom) (coeff : Fin 18 → Int) :
    RootAnnotation.trackWeight coeff (rightExpanded (.atom name)) =
      RootAnnotation.trackWeight coeff (rightCopied (.atom name)) ↔ coeff 14 = coeff 0 + coeff 9 := by
  change coeff 14 + coeff 3 = coeff 0 + (coeff 9 + coeff 3) ↔ _
  omega

theorem left_scalar_iff (name : Atom) (coeff : Fin 18 → Int) :
    RootAnnotation.trackWeight coeff (leftExpanded (.atom name)) =
      RootAnnotation.trackWeight coeff (leftCopied (.atom name)) ↔ coeff 13 = coeff 0 + coeff 9 := by
  change coeff 13 + coeff 4 = coeff 0 + (coeff 9 + coeff 4) ↔ _
  omega
theorem right_lengths (a : Shape Atom) :
    stepCount (rightExpanded a) = 2 ∧ stepCount (rightCopied a) = 3 := ⟨rfl, rfl⟩

theorem left_lengths (a : Shape Atom) :
    stepCount (leftExpanded a) = 2 ∧ stepCount (leftCopied a) = 3 := ⟨rfl, rfl⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionUnitPeak
