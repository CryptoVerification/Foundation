import Foundation.Logic.Polygraph.StructuralCartesianDistributionAnnotation

/-! Two explicit local overlaps: beta projection versus expansion of the
internal tensor in fork. The expanded route has seven rewrite leaves and
uses inverse association once. It is an equational joining path, not a
forward confluence proof. No new higher generator is postulated here. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.TensorProjectionPeak
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

/-- The first competing step expands only the tensor inside pairing. -/
def expandFst {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Step.seqLeft (.seqRight (.copy a) (.root (.tensorExpand p q))) (fst b c)

def expandSnd {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Step.seqLeft (.seqRight (.copy a) (.root (.tensorExpand p q))) (snd b c)

def fstTail {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    ProofTrack (.seq (.seq (.copy a) (fork (.seq (fst a a) p) (.seq (snd a a) q))) (fst b c)) p :=
  Track.comp (Track.step (Step.root (.assoc (.copy a) (fork (.seq (fst a a) p) (.seq (snd a a) q)) (fst b c)))) <|
  Track.comp (Track.step (Step.seqRight (.copy a) (.root (.betaFst (.seq (fst a a) p) (.seq (snd a a) q))))) <|
  Track.comp (Track.inv (Track.step (Step.root (.assoc (.copy a) (fst a a) p)))) <|
  Track.comp (Track.step (Step.seqLeft (.seqLeft (.root (.copyExpand a)) (fst a a)) p)) <|
  Track.comp (Track.step (Step.seqLeft (.root (.betaFst (.identity a) (.identity a))) p)) <|
  Track.step (Step.root (.leftId p))

def sndTail {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    ProofTrack (.seq (.seq (.copy a) (fork (.seq (fst a a) p) (.seq (snd a a) q))) (snd b c)) q :=
  Track.comp (Track.step (Step.root (.assoc (.copy a) (fork (.seq (fst a a) p) (.seq (snd a a) q)) (snd b c)))) <|
  Track.comp (Track.step (Step.seqRight (.copy a) (.root (.betaSnd (.seq (fst a a) p) (.seq (snd a a) q))))) <|
  Track.comp (Track.inv (Track.step (Step.root (.assoc (.copy a) (snd a a) q)))) <|
  Track.comp (Track.step (Step.seqLeft (.seqLeft (.root (.copyExpand a)) (snd a a)) q)) <|
  Track.comp (Track.step (Step.seqLeft (.root (.betaSnd (.identity a) (.identity a))) q)) <|
  Track.step (Step.root (.leftId q))

def fstExpanded {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp (.step (expandFst p q)) (fstTail p q)

def sndExpanded {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp (.step (expandSnd p q)) (sndTail p q)

def fstDirect {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.step (Step.root (.betaFst p q))

def sndDirect {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.step (Step.root (.betaSnd p q))

theorem fst_lengths {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    stepCount (fstExpanded p q) = 7 ∧ stepCount (fstDirect p q) = 1 := by exact ⟨rfl, rfl⟩

theorem snd_lengths {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    stepCount (sndExpanded p q) = 7 ∧ stepCount (sndDirect p q) = 1 := by exact ⟨rfl, rfl⟩

/-- Exact scalar discrepancy, with atomic output so no empty-output exception. -/
theorem fst_annotation_iff (name : Atom) (coeff : Fin 18 → Int) :
    RootAnnotation.trackWeight coeff (fstExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name))) =
      RootAnnotation.trackWeight coeff (fstDirect (Wire.identity (.atom name)) (Wire.identity (.atom name))) ↔
    coeff 8 + coeff 9 + coeff 3 + coeff 1 = 0 := by
  change coeff 8 + (coeff 0 + (coeff 3 + (-coeff 0 + (coeff 9 + (coeff 3 + coeff 1))))) = coeff 3 ↔ _
  omega

theorem snd_annotation_iff (name : Atom) (coeff : Fin 18 → Int) :
    RootAnnotation.trackWeight coeff (sndExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name))) =
      RootAnnotation.trackWeight coeff (sndDirect (Wire.identity (.atom name)) (Wire.identity (.atom name))) ↔
    coeff 8 + coeff 9 + coeff 4 + coeff 1 = 0 := by
  change coeff 8 + (coeff 0 + (coeff 4 + (-coeff 0 + (coeff 9 + (coeff 4 + coeff 1))))) = coeff 4 ↔ _
  omega

def tensorCoeff (index : Fin 18) : Int := if index.val = 8 then 1 else 0

theorem tensorCoeff_admissible : DistributionCritical.Annotation.Admissible tensorCoeff :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem fst_missing (name : Atom) : ¬ Nonempty (DistributionCritical.Cell
    (fstExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name)))
    (fstDirect (Wire.identity (.atom name)) (Wire.identity (.atom name)))) := by
  rintro ⟨cell⟩
  have same := (fst_annotation_iff name tensorCoeff).mp
    (DistributionCritical.Annotation.homotopy_weight tensorCoeff_admissible cell)
  change (1 : Int) + 0 + 0 + 0 = 0 at same
  omega

theorem snd_missing (name : Atom) : ¬ Nonempty (DistributionCritical.Cell
    (sndExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name)))
    (sndDirect (Wire.identity (.atom name)) (Wire.identity (.atom name)))) := by
  rintro ⟨cell⟩
  have same := (snd_annotation_iff name tensorCoeff).mp
    (DistributionCritical.Annotation.homotopy_weight tensorCoeff_admissible cell)
  change (1 : Int) + 0 + 0 + 0 = 0 at same
  omega

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.TensorProjectionPeak
