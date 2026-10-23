import Foundation.Logic.Polygraph.StructuralCartesianRootAnnotation

/-! Exact scalar coefficient constraints for preservation of the current
25-form pure higher basis. Necessity uses one supplied atomic shape; without
an atom the annotations can be vacuous. No completeness of the higher basis
or of all possible countermodels is inferred. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation
open CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CoherenceInvariant.weightGroup

structure Admissible (coeff : Fin 18 → Int) : Prop where
  assoc : coeff 0 = 0
  units : coeff 1 = coeff 2
  fst : coeff 5 = coeff 3
  snd : coeff 5 = coeff 4

variable {coeff : Fin 18 → Int}

theorem unitGenerator_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (generator : UnitCritical.Generator first second) :
    trackWeight coeff first = trackWeight coeff second := by
  induction generator with
  | existing old => exact generator_weight coeff old
  | unit => simp only [trackWeight, stepWeight, rootWeight, Cartesian.Root.code, valid.units]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem categoryGenerator_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (generator : CategoryCritical.Generator first second) :
    trackWeight coeff first = trackWeight coeff second := by
  induction generator with
  | existing old => exact unitGenerator_weight valid old
  | pentagon | leftUnit | middleUnit | rightUnit =>
      simp only [CategoryCritical.two, CategoryCritical.three, CategoryCritical.associate,
        CategoryCritical.leftUnit, CategoryCritical.rightUnit, trackWeight, stepWeight, rootWeight,
        Cartesian.Root.code, valid.assoc, valid.units, constant_zero,
        push_constant, CoherenceInvariant.eval_zero, add_zero, zero_add]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem productGenerator_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (generator : ProductCritical.Generator first second) :
    trackWeight coeff first = trackWeight coeff second := by
  induction generator with
  | existing old => exact categoryGenerator_weight valid old
  | fst => simp only [ProductCritical.etaFst, ProductCritical.betaEtaFst,
      trackWeight, stepWeight, rootWeight, Cartesian.Root.code, push_constant, valid.fst]
  | snd => simp only [ProductCritical.etaSnd, ProductCritical.betaEtaSnd,
      trackWeight, stepWeight, rootWeight, Cartesian.Root.code, push_constant, valid.snd]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

def Preserves (coeff : Fin 18 → Int) : Prop :=
  ∀ {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q},
    ProductCritical.Generator first second → trackWeight coeff first = trackWeight coeff second

theorem admissible_of_preserves (name : Atom) (preserves : Preserves (Atom := Atom) coeff) : Admissible coeff := by
  let a : Shape Atom := .atom name
  have pentagon := preserves (ProductCritical.Generator.existing
    (CategoryCritical.Generator.pentagon (Wire.identity a) (Wire.identity a) (Wire.identity a) (Wire.identity a)))
  have units := preserves (ProductCritical.Generator.existing
    (CategoryCritical.Generator.existing (UnitCritical.Generator.unit a)))
  have fst := preserves (ProductCritical.Generator.fst (Wire.identity (.pair a a)))
  have snd := preserves (ProductCritical.Generator.snd (Wire.identity (.pair a a)))
  change coeff 0 + coeff 0 = coeff 0 + (coeff 0 + coeff 0) at pentagon
  change coeff 1 = coeff 2 at units
  change coeff 5 = coeff 3 at fst
  change coeff 5 = coeff 4 at snd
  exact ⟨by omega, units, fst, snd⟩

theorem admissible_iff_preserves (name : Atom) : Admissible coeff ↔ Preserves (Atom := Atom) coeff :=
  ⟨fun valid _ _ _ _ _ _ generator => productGenerator_weight valid generator, admissible_of_preserves name⟩

theorem homotopy_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (cell : ProductCritical.Cell first second) :
    trackWeight coeff first = trackWeight coeff second := by
  induction cell with
  | refl => rfl
  | generator g => exact productGenerator_weight valid g
  | symm child ih => exact ih.symm
  | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
  | comp one two ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | inverse child ih => exact congrArg Neg.neg ih
  | assoc => exact add_assoc _ _ _
  | leftUnit => exact zero_add _
  | rightUnit => exact add_zero _
  | leftInv => exact neg_add_cancel _
  | rightInv => exact add_neg_cancel _

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation
