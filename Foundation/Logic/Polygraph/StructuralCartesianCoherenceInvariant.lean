import Foundation.Logic.Polygraph.StructuralCartesianTrackNaturality

/-! An algebraic countermodel for coherence of the OLD partial pure-wire basis.
Integer labels live at output atoms. A left-unit rewrite contributes one at
all outputs; other roots contribute zero. Postcomposition routes labels, and
all old local higher generators preserve the resulting track annotation.
These labels are not runtime, certificate size, probability, or proof support. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
@[reducible] def Weight : Shape Atom → Type
  | .atom _ => Int
  | .unit => PUnit
  | .pair a b => Weight a × Weight b
@[instance_reducible] def weightGroup : (a : Shape Atom) → AddCommGroup (Weight a)
  | .atom _ => inferInstance
  | .unit => inferInstance
  | .pair a b =>
      letI := weightGroup a
      letI := weightGroup b
      inferInstance
attribute [local instance] weightGroup

def ones : (a : Shape Atom) → Weight a
  | .atom _ => 1
  | .unit => PUnit.unit
  | .pair a b => (ones a, ones b)

def push : {a b : Shape Atom} → Wire a b → Weight a → Weight b
  | _, _, .identity _, x => x
  | _, _, .seq first second, x => push second (push first x)
  | _, _, .tensor first second, x => (push first x.1, push second x.2)
  | _, _, .copy _, x => (x, x)
  | _, _, .discard _, _ => PUnit.unit
  | _, _, .swap _ _, x => (x.2, x.1)
  | _, _, .assoc _ _ _, x => (x.1.1, (x.1.2, x.2))
  | _, _, .unassoc _ _ _, x => ((x.1, x.2.1), x.2.2)
  | _, _, .leftUnit _, x => x.2
  | _, _, .rightUnit _, x => x.1
  | _, _, .leftUnitInv _, x => (PUnit.unit, x)
  | _, _, .rightUnitInv _, x => (x, PUnit.unit)

theorem eval_add {a b : Shape Atom} (wire : Wire a b) (x y : Weight a) :
    push wire (x + y) = push wire x + push wire y := by
  induction wire with
  | seq one two ih₁ ih₂ => simp only [push, ih₁, ih₂]
  | tensor one two ih₁ ih₂ => exact congrArg₂ Prod.mk (ih₁ x.1 y.1) (ih₂ x.2 y.2)
  | _ => rfl

theorem eval_zero {a b : Shape Atom} (wire : Wire a b) :
    push wire (0 : Weight a) = 0 := by
  induction wire with
  | seq one two ih₁ ih₂ => simp only [push, ih₁, ih₂]
  | tensor one two ih₁ ih₂ => exact congrArg₂ Prod.mk ih₁ ih₂
  | _ => rfl

theorem eval_neg {a b : Shape Atom} (wire : Wire a b) (x : Weight a) :
    push wire (-x) = -push wire x := by
  have h := eval_add wire x (-x)
  rw [add_neg_cancel, eval_zero] at h
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm] using h.symm

def rootWeight {a b : Shape Atom} {p q : Wire a b} : Cartesian.Root p q → Weight b
  | .leftId _ => ones b
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
    (generator : Generator first second) : trackWeight first = trackWeight second := by
  induction generator with
  | argument variation change => exact argument_weight variation change
  | seqExchange first second =>
      simp only [trackWeight, stepWeight]
      rw [push_sound second, add_comm]
  | tensorExchange first second =>
      simp only [trackWeight, stepWeight, Prod.mk_add_mk, add_zero, zero_add]
  | placed place child ih => rw [placed_weight, placed_weight, ih]

theorem homotopy_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : Homotopy first second) : trackWeight first = trackWeight second := by
  induction cell with
  | refl => rfl
  | generator g => exact generator_weight g
  | symm child ih => exact ih.symm
  | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
  | comp one two ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | inverse child ih => exact congrArg Neg.neg ih
  | assoc => exact add_assoc _ _ _
  | leftUnit => exact zero_add _
  | rightUnit => exact add_zero _
  | leftInv => exact neg_add_cancel _
  | rightInv => exact add_neg_cancel _

theorem unit_overlap_not_comparable (name : Atom) :
    ¬ Nonempty (Homotopy
      (.step (.root (Cartesian.Root.leftId (Wire.identity (.atom name)))))
      (.step (.root (Cartesian.Root.rightId (Wire.identity (.atom name)))))) := by
  rintro ⟨cell⟩
  have impossible : (1 : Int) = 0 := homotopy_weight cell
  omega

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CoherenceInvariant
