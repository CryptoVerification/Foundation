import Foundation.Logic.Polygraph.StructuralCartesianProductCritical
import Foundation.Logic.Polygraph.StructuralCartesianCoherenceInvariant

/-! Integer root annotations, routed at output atoms. A coefficient is
attached to each of the actual eighteen root forms. Old argument/exchange
cells preserve every such annotation; later critical cells impose constraints.
These numbers are not probabilities, costs, or certificate sizes. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation
open CoherenceInvariant
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CoherenceInvariant.weightGroup

def constant (value : Int) : (a : Shape Atom) → Weight a
  | .atom _ => value
  | .unit => PUnit.unit
  | .pair a b => (constant value a, constant value b)

theorem constant_zero (a : Shape Atom) : constant 0 a = (0 : Weight a) := by
  induction a with
  | atom | unit => rfl
  | pair a b ih₁ ih₂ => exact congrArg₂ Prod.mk ih₁ ih₂

theorem push_constant {a b : Shape Atom} (wire : Wire a b) (value : Int) :
    push wire (constant value a) = constant value b := by
  induction wire with
  | seq first second ih₁ ih₂ => simp only [push, ih₁, ih₂]
  | tensor first second ih₁ ih₂ => exact congrArg₂ Prod.mk ih₁ ih₂
  | _ => rfl

variable (coeff : Fin 18 → Int)
def rootWeight {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q) : Weight b :=
  constant (coeff root.code) b

def stepWeight (coeff : Fin 18 → Int) : {a b : Shape Atom} → {p q : Wire a b} → Step p q → Weight b
  | _, _, _, _, .root root => rootWeight coeff root
  | _, _, _, _, .seqLeft change fixed => push fixed (stepWeight coeff change)
  | _, _, _, _, .seqRight _ change => stepWeight coeff change
  | _, _, _, _, .tensorLeft change _ => (stepWeight coeff change, 0)
  | _, _, _, _, .tensorRight _ change => (0, stepWeight coeff change)

def trackWeight (coeff : Fin 18 → Int) {a b : Shape Atom} : {p q : Wire a b} → ProofTrack p q → Weight b
  | _, _, .refl _ => 0
  | _, _, .step change => stepWeight coeff change
  | _, _, .comp first second => trackWeight coeff first + trackWeight coeff second
  | _, _, .inv child => -trackWeight coeff child

theorem seqLeft_weight {a b c : Shape Atom} {p q : Wire a b}
    (fixed : Wire b c) (path : ProofTrack p q) :
    trackWeight coeff (seqLeftTrack fixed path) = push fixed (trackWeight coeff path) := by
  induction path <;> simp_all only [seqLeftTrack, Track.map, trackWeight, stepWeight,
    eval_zero, eval_add, eval_neg]

theorem seqRight_weight {a b c : Shape Atom} (fixed : Wire a b) {p q : Wire b c}
    (path : ProofTrack p q) : trackWeight coeff (seqRightTrack fixed path) = trackWeight coeff path := by
  induction path <;> simp_all only [seqRightTrack, Track.map, trackWeight, stepWeight]

theorem tensorLeft_weight {a b c d : Shape Atom} {p q : Wire a b}
    (path : ProofTrack p q) (fixed : Wire c d) :
    trackWeight coeff (tensorLeftTrack fixed path) = (trackWeight coeff path, (0 : Weight d)) := by
  induction path <;> simp_all only [tensorLeftTrack, Track.map, trackWeight, stepWeight]
  all_goals first | rfl | simp only [Prod.mk_add_mk, add_zero, Prod.neg_mk, neg_zero]

theorem tensorRight_weight {a b c d : Shape Atom} (fixed : Wire a b) {p q : Wire c d}
    (path : ProofTrack p q) :
    trackWeight coeff (tensorRightTrack fixed path) = ((0 : Weight b), trackWeight coeff path) := by
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
    trackWeight coeff (beforeRule variation change) = trackWeight coeff (afterRule variation change) := by
  cases variation <;>
    simp only [beforeRule, afterRule, Variation.left, Variation.right, Variation.rootAt,
      Template.change, Template.pair, Template.apply, trackWeight, stepWeight, rootWeight, Cartesian.Root.code, constant,
      seqLeft_weight coeff, seqRight_weight coeff, tensorLeft_weight coeff, tensorRight_weight coeff,
      eval_zero, Cartesian.fork, Cartesian.fst, Cartesian.snd, push,
      Prod.mk_add_mk, add_zero, zero_add, pair_zero, zero_fst, zero_snd]
  all_goals
    first
    | rfl
    | exact add_comm _ _
    | exact congrArg₂ Prod.mk (add_comm _ _) rfl
    | exact congrArg₂ Prod.mk rfl (add_comm _ _)
    | exact congrArg₂ Prod.mk (add_comm _ _) (add_comm _ _)

def placeWeight {a b c d : Shape Atom} (place : Placement a b c d) (value : Weight b) : Weight d :=
  match place with
  | .seqLeft fixed => push fixed value
  | .seqRight _ => value
  | .tensorLeft _ => (value, 0)
  | .tensorRight _ => (0, value)

theorem placed_weight {a b c d : Shape Atom} (place : Placement a b c d)
    {p q : Wire a b} (path : ProofTrack p q) :
    trackWeight coeff (place.track path) = placeWeight place (trackWeight coeff path) := by
  cases place with
  | seqLeft fixed => exact seqLeft_weight coeff fixed path
  | seqRight fixed => exact seqRight_weight coeff fixed path
  | tensorLeft fixed => exact tensorLeft_weight coeff path fixed
  | tensorRight fixed => exact tensorRight_weight coeff fixed path

theorem generator_weight {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Cartesian.Higher.Generator first second) : trackWeight coeff first = trackWeight coeff second := by
  induction generator with
  | argument variation change => exact argument_weight coeff variation change
  | seqExchange first second =>
      simp only [trackWeight, stepWeight]
      rw [push_sound second, add_comm]
  | tensorExchange first second =>
      simp only [trackWeight, stepWeight, Prod.mk_add_mk, add_zero, zero_add]
  | placed place child ih => rw [placed_weight coeff, placed_weight coeff, ih]


end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation
