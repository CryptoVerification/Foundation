import Foundation.Logic.Polygraph.StructuralCartesianExpansionCritical

/-! Exact preservation constraints within the constant-output eighteen-root
integer annotation class for the 31-form extension. This is neither higher
coherence nor classification of all countermodels. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.Annotation
open CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CoherenceInvariant.weightGroup

theorem constant_add (x y : Int) (a : Shape Atom) :
    RootAnnotation.constant (x + y) a = RootAnnotation.constant x a + RootAnnotation.constant y a := by
  induction a with
  | atom | unit => rfl
  | pair a b one two => exact congrArg₂ Prod.mk one two

structure Admissible (coeff : Fin 18 → Int) : Prop extends toDistribution : DistributionCritical.Annotation.Admissible coeff where
  tensor : coeff 8 + coeff 9 + coeff 3 + coeff 1 = 0
  leftUnit : coeff 13 = coeff 9
  rightUnit : coeff 14 = coeff 9

variable {coeff : Fin 18 → Int}

theorem generator_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (generator : ExpansionCritical.Generator first second) :
    RootAnnotation.trackWeight coeff first = RootAnnotation.trackWeight coeff second := by
  induction generator with
  | existing old => exact DistributionCritical.Annotation.generator_weight valid.toDistribution old
  | fst =>
      simp only [TensorProjectionPeak.fstExpanded, TensorProjectionPeak.fstDirect,
        TensorProjectionPeak.expandFst, TensorProjectionPeak.fstTail,
        RootAnnotation.trackWeight, RootAnnotation.stepWeight, RootAnnotation.rootWeight,
        Cartesian.Root.code, valid.assoc, RootAnnotation.constant_zero,
        neg_zero, zero_add, RootAnnotation.push_constant,
        ← constant_add]
      apply congrArg (fun z => RootAnnotation.constant z _)
      have scalar := valid.tensor
      omega
  | snd =>
      simp only [TensorProjectionPeak.sndExpanded, TensorProjectionPeak.sndDirect,
        TensorProjectionPeak.expandSnd, TensorProjectionPeak.sndTail,
        RootAnnotation.trackWeight, RootAnnotation.stepWeight, RootAnnotation.rootWeight,
        Cartesian.Root.code, valid.assoc, RootAnnotation.constant_zero,
        neg_zero, zero_add, RootAnnotation.push_constant,
        ← constant_add]
      apply congrArg (fun z => RootAnnotation.constant z _)
      have scalar := valid.tensor
      have first := valid.fst
      have second := valid.snd
      omega
  | leftUnit | rightUnit =>
      simp only [ExpansionUnitPeak.leftExpanded, ExpansionUnitPeak.leftCopied,
        ExpansionUnitPeak.rightExpanded, ExpansionUnitPeak.rightCopied,
        RootAnnotation.trackWeight, RootAnnotation.stepWeight, RootAnnotation.rootWeight,
        Cartesian.Root.code, valid.assoc, valid.leftUnit, valid.rightUnit,
        RootAnnotation.constant_zero, zero_add, RootAnnotation.push_constant]
  | placed place child ih => rw [RootAnnotation.placed_weight, RootAnnotation.placed_weight, ih]

def Preserves (coeff : Fin 18 → Int) : Prop :=
  ∀ {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q},
    ExpansionCritical.Generator first second → RootAnnotation.trackWeight coeff first = RootAnnotation.trackWeight coeff second

theorem admissible_of_preserves (name : Atom) (preserves : Preserves (Atom := Atom) coeff) : Admissible coeff := by
  have old := DistributionCritical.Annotation.admissible_of_preserves name
    (fun generator => preserves (.existing generator))
  have tensor := (TensorProjectionPeak.fst_annotation_iff name coeff).mp
    (preserves (.fst (Wire.identity (.atom name)) (Wire.identity (.atom name))))
  have left := (ExpansionUnitPeak.left_scalar_iff name coeff).mp (preserves (.leftUnit (.atom name)))
  have right := (ExpansionUnitPeak.right_scalar_iff name coeff).mp (preserves (.rightUnit (.atom name)))
  exact ⟨old, tensor, by simpa only [old.assoc, zero_add] using left,
    by simpa only [old.assoc, zero_add] using right⟩

theorem admissible_iff_preserves (name : Atom) : Admissible coeff ↔ Preserves (Atom := Atom) coeff :=
  ⟨fun valid _ _ _ _ _ _ generator => generator_weight valid generator, admissible_of_preserves name⟩

theorem homotopy_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (cell : ExpansionCritical.Cell first second) :
    RootAnnotation.trackWeight coeff first = RootAnnotation.trackWeight coeff second := by
  induction cell with
  | refl => rfl
  | generator g => exact generator_weight valid g
  | symm child ih => exact ih.symm
  | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
  | comp one two ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | inverse child ih => exact congrArg Neg.neg ih
  | assoc => exact add_assoc _ _ _
  | leftUnit => exact zero_add _
  | rightUnit => exact add_zero _
  | leftInv => exact neg_add_cancel _
  | rightInv => exact add_neg_cancel _

def rightUnitCoeff (index : Fin 18) : Int := if index.val = 14 then 1 else 0

theorem rightUnitCoeff_admissible : DistributionCritical.Annotation.Admissible rightUnitCoeff :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem rightUnit_missing_before (name : Atom) : ¬ Nonempty (DistributionCritical.Cell
    (ExpansionUnitPeak.rightExpanded (.atom name)) (ExpansionUnitPeak.rightCopied (.atom name))) := by
  rintro ⟨cell⟩
  have scalar := (ExpansionUnitPeak.right_scalar_iff name rightUnitCoeff).mp
    (DistributionCritical.Annotation.homotopy_weight rightUnitCoeff_admissible cell)
  change (1 : Int) = 0 + 0 at scalar
  omega

theorem strict_extension (name : Atom) :
    Nonempty (ExpansionCritical.Cell (TensorProjectionPeak.fstExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name)))
      (TensorProjectionPeak.fstDirect (Wire.identity (.atom name)) (Wire.identity (.atom name)))) ∧
    ¬ Nonempty (DistributionCritical.Cell (TensorProjectionPeak.fstExpanded (Wire.identity (.atom name)) (Wire.identity (.atom name)))
      (TensorProjectionPeak.fstDirect (Wire.identity (.atom name)) (Wire.identity (.atom name)))) :=
  ⟨⟨fstCell _ _⟩, TensorProjectionPeak.fst_missing name⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.Annotation
