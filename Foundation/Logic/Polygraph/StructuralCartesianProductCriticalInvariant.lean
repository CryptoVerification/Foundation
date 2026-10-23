import Foundation.Logic.Polygraph.StructuralCartesianProductCritical
import Foundation.Logic.Polygraph.StructuralCartesianCoherenceInvariant

/-! A different output annotation detects product critical diagrams still
missing AFTER adding categorical critical diagrams. Eta contributes one to
all output atoms. These annotations are not resources or probabilities. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical.Invariant
open CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CoherenceInvariant.weightGroup

def rootWeight {a b : Shape Atom} {p q : Wire a b} : Cartesian.Root p q → Weight b
  | .eta _ => ones _
  | _ => 0

def stepWeight : {a b : Shape Atom} → {p q : Wire a b} → Step p q → Weight b
  | _, _, _, _, .root root => rootWeight root
  | _, _, _, _, .seqLeft change fixed => push fixed (stepWeight change)
  | _, _, _, _, .seqRight _ change => stepWeight change
  | _, _, _, _, .tensorLeft change _ => (stepWeight change, 0)
  | _, _, _, _, .tensorRight _ change => (0, stepWeight change)

def trackWeight {a b : Shape Atom} : {p q : Wire a b} → ProofTrack p q → Weight b
  | _, _, .refl _ => 0
  | _, _, .step change => stepWeight change
  | _, _, .comp first second => trackWeight first + trackWeight second
  | _, _, .inv child => -trackWeight child

theorem seqLeft_weight {a b c : Shape Atom} {p q : Wire a b}
    (fixed : Wire b c) (path : ProofTrack p q) :
    trackWeight (seqLeftTrack fixed path) = push fixed (trackWeight path) := by
  induction path <;> simp_all only [seqLeftTrack, Track.map, trackWeight, stepWeight,
    eval_zero, eval_add, eval_neg]

theorem seqRight_weight {a b c : Shape Atom} (fixed : Wire a b) {p q : Wire b c}
    (path : ProofTrack p q) : trackWeight (seqRightTrack fixed path) = trackWeight path := by
  induction path <;> simp_all only [seqRightTrack, Track.map, trackWeight, stepWeight]

theorem tensorLeft_weight {a b c d : Shape Atom} {p q : Wire a b}
    (path : ProofTrack p q) (fixed : Wire c d) :
    trackWeight (tensorLeftTrack fixed path) = (trackWeight path, (0 : Weight d)) := by
  induction path <;> simp_all only [tensorLeftTrack, Track.map, trackWeight, stepWeight]
  all_goals first | rfl | simp only [Prod.mk_add_mk, add_zero, Prod.neg_mk, neg_zero]

theorem tensorRight_weight {a b c d : Shape Atom} (fixed : Wire a b) {p q : Wire c d}
    (path : ProofTrack p q) :
    trackWeight (tensorRightTrack fixed path) = ((0 : Weight b), trackWeight path) := by
  induction path <;> simp_all only [tensorRightTrack, Track.map, trackWeight, stepWeight]
  all_goals first | rfl | simp only [Prod.mk_add_mk, zero_add, Prod.neg_mk, neg_zero]

theorem push_sound {a b : Shape Atom} {p q : Wire a b} (change : Step p q) (x : Weight a) :
    push p x = push q x := by
  induction change with
  | root root => cases root <;> rfl
  | seqLeft change fixed ih => exact congrArg (push fixed) (ih x)
  | seqRight fixed change ih => exact ih (push fixed x)
  | tensorLeft change fixed ih => exact congrArg (fun v => (v, push fixed x.2)) (ih x.1)
  | tensorRight fixed change ih => exact congrArg (fun v => (push fixed x.1, v)) (ih x.2)

private theorem pair_zero {a b : Shape Atom} : ((0 : Weight a), (0 : Weight b)) = (0 : Weight (.pair a b)) := rfl

private theorem zero_fst {a b : Shape Atom} : (0 : Weight (.pair a b)).1 = (0 : Weight a) := rfl
private theorem zero_snd {a b : Shape Atom} : (0 : Weight (.pair a b)).2 = (0 : Weight b) := rfl

theorem argument_weight {u v a b : Shape Atom} (variation : Variation u v a b)
    {p q : Wire u v} (change : Step p q) :
    trackWeight (beforeRule variation change) = trackWeight (afterRule variation change) := by
  cases variation <;>
    simp only [beforeRule, afterRule, Variation.left, Variation.right, Variation.rootAt,
      Template.change, Template.pair, Template.apply, trackWeight, stepWeight, rootWeight,
      seqLeft_weight, seqRight_weight, tensorLeft_weight, tensorRight_weight,
      eval_zero, Cartesian.fork, Cartesian.fst, Cartesian.snd, push,
      Prod.mk_add_mk, add_zero, zero_add, pair_zero, zero_fst, zero_snd]
  all_goals first | rfl | exact add_comm _ _

def placeWeight {a b c d : Shape Atom} (place : Placement a b c d) (value : Weight b) : Weight d :=
  match place with
  | .seqLeft fixed => push fixed value
  | .seqRight _ => value
  | .tensorLeft _ => (value, 0)
  | .tensorRight _ => (0, value)

theorem placed_weight {a b c d : Shape Atom} (place : Placement a b c d)
    {p q : Wire a b} (path : ProofTrack p q) :
    trackWeight (place.track path) = placeWeight place (trackWeight path) := by
  cases place with
  | seqLeft fixed => exact seqLeft_weight fixed path
  | seqRight fixed => exact seqRight_weight fixed path
  | tensorLeft fixed => exact tensorLeft_weight path fixed
  | tensorRight fixed => exact tensorRight_weight fixed path

theorem generator_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Cartesian.Higher.Generator first second) : trackWeight first = trackWeight second := by
  induction generator with
  | argument variation change => exact argument_weight variation change
  | seqExchange first second =>
      simp only [trackWeight, stepWeight]
      rw [push_sound second, add_comm]
  | tensorExchange first second =>
      simp only [trackWeight, stepWeight, Prod.mk_add_mk, add_zero, zero_add]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem unitGenerator_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : UnitCritical.Generator first second) : trackWeight first = trackWeight second := by
  induction generator with
  | existing old => exact generator_weight old
  | unit => rfl
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem categoryGenerator_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : CategoryCritical.Generator first second) : trackWeight first = trackWeight second := by
  induction generator with
  | existing old => exact unitGenerator_weight old
  | pentagon | leftUnit | middleUnit | rightUnit =>
      simp only [CategoryCritical.two, CategoryCritical.three, CategoryCritical.associate,
        CategoryCritical.leftUnit, CategoryCritical.rightUnit, trackWeight, stepWeight, rootWeight,
        CoherenceInvariant.eval_zero, add_zero]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem homotopy_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : CategoryCritical.Cell first second) : trackWeight first = trackWeight second := by
  induction cell with
  | refl => rfl
  | generator g => exact categoryGenerator_weight g
  | symm child ih => exact ih.symm
  | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
  | comp one two ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | inverse child ih => exact congrArg Neg.neg ih
  | assoc => exact add_assoc _ _ _
  | leftUnit => exact zero_add _
  | rightUnit => exact add_zero _
  | leftInv => exact neg_add_cancel _
  | rightInv => exact add_neg_cancel _

def atomicPairIdentity (name : Atom) : Wire (.pair (.atom name) (.atom name)) (.pair (.atom name) (.atom name)) := .identity _
def atomicIdentity (name : Atom) : Wire (.atom name) (.atom name) := .identity _

theorem fst_not_comparable (name : Atom) :
    ¬ Nonempty (CategoryCritical.Cell (etaFst (atomicPairIdentity name)) (betaEtaFst (atomicPairIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := homotopy_weight cell
  omega

theorem snd_not_comparable (name : Atom) :
    ¬ Nonempty (CategoryCritical.Cell (etaSnd (atomicPairIdentity name)) (betaEtaSnd (atomicPairIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := homotopy_weight cell
  omega

theorem fork_not_comparable (name : Atom) :
    ¬ Nonempty (CategoryCritical.Cell (forkBeta (atomicIdentity name) (atomicIdentity name))
      (forkEta (atomicIdentity name) (atomicIdentity name))) := by
  rintro ⟨cell⟩
  have impossible : (0 : Int) = 1 := congrArg Prod.fst (homotopy_weight cell)
  omega

theorem strict_extension (name : Atom) :
    Nonempty (ProductCritical.Cell (etaFst (atomicPairIdentity name)) (betaEtaFst (atomicPairIdentity name))) ∧
    ¬ Nonempty (CategoryCritical.Cell (etaFst (atomicPairIdentity name)) (betaEtaFst (atomicPairIdentity name))) :=
  ⟨⟨fstCell _⟩, fst_not_comparable name⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical.Invariant
