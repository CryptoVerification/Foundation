import Foundation.Logic.Polygraph.StructuralCartesianRootAnnotationCritical
import Foundation.Logic.Polygraph.StructuralCartesianDistributionUnitCoherence

/-! Exact annotation constraints for the 27-form distribution extension.
The new diagrams impose coefficient 7 = 0. This scalar countermodel class
also proves concrete strictness over the previous product-critical basis.
It does not classify every possible invariant or establish full coherence. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical.Annotation
open CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CoherenceInvariant.weightGroup

structure Admissible (coeff : Fin 18 → Int) : Prop extends RootAnnotation.Admissible coeff where
  distribution : coeff 7 = 0

variable {coeff : Fin 18 → Int}

theorem generator_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (generator : DistributionCritical.Generator first second) :
    RootAnnotation.trackWeight coeff first = RootAnnotation.trackWeight coeff second := by
  induction generator with
  | existing old => exact RootAnnotation.productGenerator_weight valid.toAdmissible old
  | fst | snd =>
      simp only [fstDistributed, fstAssociated, sndDistributed, sndAssociated,
        RootAnnotation.trackWeight, RootAnnotation.stepWeight, RootAnnotation.rootWeight,
        Cartesian.Root.code, CoherenceInvariant.eval_zero, valid.assoc, valid.distribution,
        RootAnnotation.constant_zero, zero_add]
  | placed place child ih => rw [RootAnnotation.placed_weight, RootAnnotation.placed_weight, ih]

def Preserves (coeff : Fin 18 → Int) : Prop :=
  ∀ {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q},
    DistributionCritical.Generator first second → RootAnnotation.trackWeight coeff first = RootAnnotation.trackWeight coeff second

theorem admissible_of_preserves (name : Atom) (preserves : Preserves (Atom := Atom) coeff) : Admissible coeff := by
  have old : RootAnnotation.Admissible coeff := RootAnnotation.admissible_of_preserves name
    (fun generator => preserves (.existing generator))
  let a : Shape Atom := .atom name
  have projected := preserves (DistributionCritical.Generator.fst (Wire.identity a) (Wire.identity a) (Wire.identity a))
  change coeff 7 + coeff 3 = coeff 0 + coeff 3 at projected
  exact ⟨old, by have zero := old.assoc; omega⟩

theorem admissible_iff_preserves (name : Atom) : Admissible coeff ↔ Preserves (Atom := Atom) coeff :=
  ⟨fun valid _ _ _ _ _ _ generator => generator_weight valid generator, admissible_of_preserves name⟩

theorem homotopy_weight (valid : Admissible coeff) {a b : Shape Atom} {p q : Wire a b}
    {first second : ProofTrack p q} (cell : DistributionCritical.Cell first second) :
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

def forkCoeff (index : Fin 18) : Int := if index.val = 7 then 1 else 0

theorem forkCoeff_admissible : RootAnnotation.Admissible forkCoeff := ⟨rfl, rfl, rfl, rfl⟩

def atomicIdentity (name : Atom) : Wire (.atom name) (.atom name) := .identity _

theorem fst_not_comparable (name : Atom) :
    ¬ Nonempty (ProductCritical.Cell
      (fstDistributed (atomicIdentity name) (atomicIdentity name) (atomicIdentity name))
      (fstAssociated (atomicIdentity name) (atomicIdentity name) (atomicIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := RootAnnotation.homotopy_weight forkCoeff_admissible cell
  omega

theorem snd_not_comparable (name : Atom) :
    ¬ Nonempty (ProductCritical.Cell
      (sndDistributed (atomicIdentity name) (atomicIdentity name) (atomicIdentity name))
      (sndAssociated (atomicIdentity name) (atomicIdentity name) (atomicIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := RootAnnotation.homotopy_weight forkCoeff_admissible cell
  omega

theorem identity_not_comparable (name : Atom) :
    ¬ Nonempty (ProductCritical.Cell
      (identityDistributed (atomicIdentity name) (atomicIdentity name))
      (identityDirect (atomicIdentity name) (atomicIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := congrArg Prod.fst (RootAnnotation.homotopy_weight forkCoeff_admissible cell)
  omega

theorem strict_extension (name : Atom) :
    Nonempty (DistributionCritical.Cell
      (identityDistributed (atomicIdentity name) (atomicIdentity name))
      (identityDirect (atomicIdentity name) (atomicIdentity name))) ∧
    ¬ Nonempty (ProductCritical.Cell
      (identityDistributed (atomicIdentity name) (atomicIdentity name))
      (identityDirect (atomicIdentity name) (atomicIdentity name))) :=
  ⟨⟨identityCell _ _⟩, identity_not_comparable name⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical.Annotation
