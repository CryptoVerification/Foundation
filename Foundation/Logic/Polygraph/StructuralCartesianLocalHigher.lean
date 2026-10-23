import Foundation.Logic.Polygraph.StructuralCartesianArgumentCoverage
import Foundation.Logic.Polygraph.Higher

/-! Explicit local higher generators: sixteen argument-naturality forms and
two separated exchange forms, closed under four single-hole placements.
All generator boundaries have at most three actual rewrite edges. This is
NOT an exhaustive higher critical basis or a global coherence theorem. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Placement : Shape Atom → Shape Atom → Shape Atom → Shape Atom → Type where
  | seqLeft {a b c} (fixed : Wire b c) : Placement a b a c
  | seqRight {a b c} (fixed : Wire a b) : Placement b c a c
  | tensorLeft {a b c d} (fixed : Wire c d) : Placement a b (.pair a c) (.pair b d)
  | tensorRight {a b c d} (fixed : Wire a b) : Placement c d (.pair a c) (.pair b d)

namespace Placement

def apply : {a b c d : Shape Atom} → Placement a b c d → Wire a b → Wire c d
  | _, _, _, _, .seqLeft fixed, wire => .seq wire fixed
  | _, _, _, _, .seqRight fixed, wire => .seq fixed wire
  | _, _, _, _, .tensorLeft fixed, wire => .tensor wire fixed
  | _, _, _, _, .tensorRight fixed, wire => .tensor fixed wire

def step : {a b c d : Shape Atom} → (place : Placement a b c d) → {p q : Wire a b} →
    Step p q → Step (place.apply p) (place.apply q)
  | _, _, _, _, .seqLeft fixed, _, _, change => .seqLeft change fixed
  | _, _, _, _, .seqRight fixed, _, _, change => .seqRight fixed change
  | _, _, _, _, .tensorLeft fixed, _, _, change => .tensorLeft change fixed
  | _, _, _, _, .tensorRight fixed, _, _, change => .tensorRight fixed change

def track {a b c d : Shape Atom} (place : Placement a b c d) {p q : Wire a b} (path : ProofTrack p q) :
    ProofTrack (place.apply p) (place.apply q) := path.map place.apply (fun change => place.step change)

theorem track_count {a b c d : Shape Atom} (place : Placement a b c d) {p q : Wire a b} (path : ProofTrack p q) :
    stepCount (place.track path) = stepCount path := stepCount_map _ _ _

end Placement

def beforeRule {u v a b : Shape Atom} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
    ProofTrack (variation.left.apply p) (variation.right.apply q) :=
  .comp (variation.left.change change) (.step (.root (variation.rootAt q)))

def afterRule {u v a b : Shape Atom} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
    ProofTrack (variation.left.apply p) (variation.right.apply q) :=
  .comp (.step (.root (variation.rootAt p))) (variation.right.change change)

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | argument {u v a b} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
      Generator (beforeRule variation change) (afterRule variation change)
  | seqExchange {a b c} {p p' : Wire a b} {q q' : Wire b c} (first : Step p p') (second : Step q q') :
      Generator (.comp (.step (.seqLeft first q)) (.step (.seqRight p' second)))
        (.comp (.step (.seqRight p second)) (.step (.seqLeft first q')))
  | tensorExchange {a b c d} {p p' : Wire a b} {q q' : Wire c d} (first : Step p p') (second : Step q q') :
      Generator (.comp (.step (.tensorLeft first q)) (.step (.tensorRight p' second)))
        (.comp (.step (.tensorRight p second)) (.step (.tensorLeft first q')))
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

/-- Underlying local family tag; contextual placement does not add a new
base family. This is not a classifier for arbitrary critical overlaps. -/
def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} → Generator first second → Fin 18
  | _, _, _, _, _, _, .argument variation _ => Fin.castAdd 2 variation.code
  | _, _, _, _, _, _, .seqExchange _ _ => 16
  | _, _, _, _, _, _, .tensorExchange _ _ => 17
  | _, _, _, _, _, _, .placed _ child => child.code

abbrev Homotopy {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def argumentCell {u v a b : Shape Atom} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
    Homotopy (beforeRule variation change) (afterRule variation change) := .generator (.argument variation change)

theorem beforeRule_count {u v a b : Shape Atom} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
    stepCount (beforeRule variation change) = variation.left.holes + 1 := by
  simp only [beforeRule, stepCount, Template.change_count]

theorem afterRule_count {u v a b : Shape Atom} (variation : Variation u v a b) {p q : Wire u v} (change : Step p q) :
    stepCount (afterRule variation change) = 1 + variation.right.holes := by
  simp only [afterRule, stepCount, Template.change_count]

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 3 ∧ stepCount second ≤ 3 := by
  induction generator with
  | argument variation change =>
      rw [beforeRule_count, afterRule_count]
      have one := variation.left_holes_le_two
      have two := variation.right_holes_le_two
      omega
  | seqExchange | tensorExchange => decide_cbv
  | placed place child ih => simpa only [Placement.track_count] using ih

namespace Homotopy

def whisker {a b c d : Shape Atom} (place : Placement a b c d) : {p q : Wire a b} →
    {first second : ProofTrack p q} → Homotopy first second → Homotopy (place.track first) (place.track second)
  | _, _, _, _, .refl path => .refl _
  | _, _, _, _, .generator generator => .generator (.placed place generator)
  | _, _, _, _, .symm child => (whisker place child).symm
  | _, _, _, _, .trans first second => (whisker place first).trans (whisker place second)
  | _, _, _, _, .comp first second => .comp (whisker place first) (whisker place second)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc p q r => .assoc _ _ _
  | _, _, _, _, .leftUnit p => .leftUnit _
  | _, _, _, _, .rightUnit p => .rightUnit _
  | _, _, _, _, .leftInv p => .leftInv _
  | _, _, _, _, .rightInv p => .rightInv _

def constructorCount {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} → Homotopy first second → Nat
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => 1 + constructorCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => 1 + constructorCount first + constructorCount second
  | _, _, _, _, _ => 1

theorem whisker_constructorCount {a b c d : Shape Atom} (place : Placement a b c d) {p q : Wire a b}
    {first second : ProofTrack p q} (cell : Homotopy first second) : constructorCount (cell.whisker place) = constructorCount cell := by
  induction cell <;> simp_all only [whisker, constructorCount]

/-- Counts supplied local generators, excluding groupoid law constructors
and all path/context/Wire payloads. -/
def generatorCount {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} → Homotopy first second → Nat
  | _, _, _, _, .generator _ => 1
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => generatorCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => generatorCount first + generatorCount second
  | _, _, _, _, _ => 0

/-- A triangle for one actual change inside a subsequently discarded wire. -/
def discardStep {a b : Shape Atom} {p q : Wire a b} (change : Step p q) :
    Homotopy (.comp (.step (.seqLeft change (.discard b))) (.step (.root (.discardAfter q))))
      (.step (.root (.discardAfter p))) :=
  (Four.comp (Four.rightUnit (G := Generator) (.step (.seqLeft change (.discard b)))).symm (Four.refl _)).trans
    ((argumentCell (Variation.discard a b) change).trans (Four.rightUnit _))

/-- Construct a comparison for an arbitrary inner proof path followed by
terminality, using only the one-step discard diagram and groupoid laws. -/
def discardTrack {a b : Shape Atom} : {p q : Wire a b} → (path : ProofTrack p q) →
    Homotopy (.comp (seqLeftTrack (.discard b) path) (.step (.root (.discardAfter q))))
      (.step (.root (.discardAfter p)))
  | _, _, .refl _ => .leftUnit _
  | _, _, .step change => discardStep change
  | _, _, .comp first second =>
      (Four.assoc _ _ _).trans
        ((Four.comp (.refl _) (discardTrack second)).trans (discardTrack first))
  | _, _, .inv child =>
      (Four.comp (.refl _) (discardTrack child).symm).trans
        ((Four.assoc _ _ _).symm.trans
          ((Four.comp (Four.leftInv _) (.refl _)).trans (Four.leftUnit _)))

/-- Cancellation here removes a COMMON REWRITE-PROOF suffix. It does not
cancel a wire operation, a stochastic kernel, or discarded observations. -/
def cancelRight {a b : Shape Atom} {p q r : Wire a b} {first second : ProofTrack p q}
    (suffix : ProofTrack q r) (square : Homotopy (.comp first suffix) (.comp second suffix)) : Homotopy first second :=
  (Four.rightUnit (G := Generator) first).symm.trans
    ((Four.comp (.refl first) (Four.rightInv suffix).symm).trans
      ((Four.assoc first suffix (.inv suffix)).symm.trans
        ((Four.comp square (.refl (.inv suffix))).trans
          ((Four.assoc second suffix (.inv suffix)).trans
            ((Four.comp (.refl second) (Four.rightInv suffix)).trans (Four.rightUnit second))))))

/-- Every pair of parallel INNER proof paths becomes comparable after
postcomposition with discard. This makes no claim of coherence before discard. -/
def discardedParallel {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :
    Homotopy (seqLeftTrack (.discard b) first) (seqLeftTrack (.discard b) second) :=
  cancelRight (.step (.root (.discardAfter q))) ((discardTrack first).trans (discardTrack second).symm)

theorem discardTrack_generatorCount {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    generatorCount (discardTrack path) = stepCount path := by
  induction path <;> simp_all only [discardTrack, discardStep, argumentCell, generatorCount, stepCount, Nat.zero_add, Nat.add_zero]
  omega

theorem discardedParallel_generatorCount {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :
    generatorCount (discardedParallel first second) = stepCount first + stepCount second := by
  simp only [discardedParallel, cancelRight, generatorCount, discardTrack_generatorCount, Nat.zero_add, Nat.add_zero]

theorem discardTrack_constructorBound {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    constructorCount (discardTrack path) ≤ 12 * trackConstructorCount path := by
  induction path <;> simp_all only [discardTrack, discardStep, argumentCell, constructorCount, trackConstructorCount] <;> omega

theorem discardedParallel_constructorBound {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :
    constructorCount (discardedParallel first second) ≤
      23 + 12 * (trackConstructorCount first + trackConstructorCount second) := by
  have one := discardTrack_constructorBound first
  have two := discardTrack_constructorBound second
  simp only [discardedParallel, cancelRight, constructorCount]
  omega

end Homotopy
end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
