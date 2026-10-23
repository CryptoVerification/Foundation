import Foundation.Crypto.Logic.Polygraph.MixedCircuitNormalization
import Foundation.Logic.Polygraph.Higher

/-! Proof-relevant higher cells for mixed rewrite proofs. The sole extra
family is a separated two-step exchange, built from the four split placements
and four context placements of Separated. No arbitrary parallel-path or
normalization square is a primitive. Formal inverse reverses a rewrite proof,
not a stochastic execution kernel. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Logic.Polygraph
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

abbrev RewriteTrack {n m} (a b : Circuit signature n m) := Track (fun x y => Step relators x y) a b

def route {n m} {a b c : Circuit signature n m} (change : Step relators a b) (tail : Path (relators := relators) b c) :
    RewriteTrack (relators := relators) a c := .comp (.step change) (Track.ofPath tail)

inductive Placement : Port signature → Port signature → Port signature → Port signature → Type where
  | seqLeft {a b c} (fixed : Circuit signature b c) : Placement a b a c
  | seqRight {a b c} (fixed : Circuit signature a b) : Placement b c a c
  | tensorLeft {a b c d} (fixed : Circuit signature c d) : Placement a b (.pair a c) (.pair b d)
  | tensorRight {a b c d} (fixed : Circuit signature a b) : Placement c d (.pair a c) (.pair b d)

namespace Placement

def apply : {a b c d : Port signature} → Placement a b c d → Circuit signature a b → Circuit signature c d
  | _, _, _, _, .seqLeft fixed, circuit => .seq circuit fixed
  | _, _, _, _, .seqRight fixed, circuit => .seq fixed circuit
  | _, _, _, _, .tensorLeft fixed, circuit => .tensor circuit fixed
  | _, _, _, _, .tensorRight fixed, circuit => .tensor fixed circuit

def step : {a b c d : Port signature} → (place : Placement a b c d) →
    {x y : Circuit signature a b} → Step relators x y → Step relators (place.apply x) (place.apply y)
  | _, _, _, _, .seqLeft fixed, _, _, change => .seqLeft change fixed
  | _, _, _, _, .seqRight fixed, _, _, change => .seqRight fixed change
  | _, _, _, _, .tensorLeft fixed, _, _, change => .tensorLeft change fixed
  | _, _, _, _, .tensorRight fixed, _, _, change => .tensorRight fixed change

def separate {a b c d} (place : Placement (signature := signature) a b c d) {x y z : Circuit signature a b}
    {s : Step relators x y} {t : Step relators x z} (witness : Separated s t) : Separated (place.step s) (place.step t) :=
  match place with
  | .seqLeft fixed => .seqLeft witness fixed
  | .seqRight fixed => .seqRight fixed witness
  | .tensorLeft fixed => .tensorLeft witness fixed
  | .tensorRight fixed => .tensorRight fixed witness

def track {a b c d} (place : Placement (signature := signature) a b c d) {x y : Circuit signature a b}
    (path : RewriteTrack (relators := relators) x y) : RewriteTrack (relators := relators) (place.apply x) (place.apply y) :=
  path.map place.apply (fun change => place.step change)

def needs : {a b c d : Port signature} → Placement a b c d → Finset Requirement
  | _, _, _, _, .seqLeft fixed | _, _, _, _, .seqRight fixed => fixed.needs
  | _, _, _, _, .tensorLeft fixed | _, _, _, _, .tensorRight fixed => fixed.needs

end Placement

/-- Each boundary has two actual rewrite steps, irrespective of the depth
of their placements. Separated itself is built from finite local forms. -/
inductive Exchange : {n m : Port signature} → {a b : Circuit signature n m} →
    RewriteTrack (relators := relators) a b → RewriteTrack (relators := relators) a b → Type where
  | separated {n m} {a b c : Circuit signature n m} {first : Step relators a b} {second : Step relators a c}
      (witness : Separated first second) :
      Exchange (route first (RewritePath.single witness.diamond.afterFirst))
        (route second (RewritePath.single witness.diamond.afterSecond))

namespace Exchange

def whisker {a b c d} (place : Placement (signature := signature) a b c d) {x y : Circuit signature a b}
    {p q : RewriteTrack (relators := relators) x y} (generator : Exchange p q) : Exchange (place.track p) (place.track q) := by
  cases generator with
  | separated witness =>
      cases place with
      | seqLeft fixed => exact .separated (.seqLeft witness fixed)
      | seqRight fixed => exact .separated (.seqRight fixed witness)
      | tensorLeft fixed => exact .separated (.tensorLeft witness fixed)
      | tensorRight fixed => exact .separated (.tensorRight fixed witness)

def support {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (generator : Exchange p q) : Finset Requirement :=
  match generator with
  | .separated (first := first) (second := second) _ => first.support ∪ second.support

end Exchange

abbrev Homotopy {n m} {a b : Circuit signature n m} (p q : RewriteTrack (relators := relators) a b) :=
  Four (Exchange (relators := relators)) p q

namespace Homotopy

/-- Context lifting maps the existing separated witness; it is not a new
whole-path comparison generator. -/
def whisker {a b c d} (place : Placement (signature := signature) a b c d) :
    {x y : Circuit signature a b} → {p q : RewriteTrack (relators := relators) x y} → Homotopy p q →
    Homotopy (place.track p) (place.track q)
  | _, _, _, _, .refl p => .refl _
  | _, _, _, _, .generator generator => .generator (generator.whisker place)
  | _, _, _, _, .symm cell => (whisker place cell).symm
  | _, _, _, _, .trans first second => (whisker place first).trans (whisker place second)
  | _, _, _, _, .comp first second => .comp (whisker place first) (whisker place second)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc p q r => .assoc _ _ _
  | _, _, _, _, .leftUnit p => .leftUnit _
  | _, _, _, _, .rightUnit p => .rightUnit _
  | _, _, _, _, .leftInv p => .leftInv _
  | _, _, _, _, .rightInv p => .rightInv _

end Homotopy

namespace RewriteTrack

def support {n m : Port signature} : {a b : Circuit signature n m} → RewriteTrack (relators := relators) a b → Finset Requirement
  | _, _, .refl circuit => circuit.needs
  | _, _, .step change => change.support
  | _, _, .comp first second => support first ∪ support second
  | _, _, .inv child => support child

theorem boundaries {n m} {a b : Circuit signature n m} (path : RewriteTrack (relators := relators) a b) :
    a.needs ⊆ support path ∧ b.needs ⊆ support path := by
  induction path with
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | step change => exact change.boundaries
  | comp first second one two =>
      exact ⟨fun _ h => Finset.mem_union_left _ (one.1 h), fun _ h => Finset.mem_union_right _ (two.2 h)⟩
  | inv child ih => exact ⟨ih.2, ih.1⟩

theorem ofPath_support {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) :
    support (Track.ofPath path) = Path.support path := by
  induction path with
  | refl => rfl
  | cons change tail ih => simp only [Track.ofPath, support, Path.support, ih]

theorem sound {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators condition Value) {n m} {a b : Circuit signature n m}
    (path : RewriteTrack (relators := relators) a b) (valid : Holds condition (support path))
    (left : Holds condition a.needs) (right : Holds condition b.needs) (input : Bundle Value n) :
    evaluate model.base a left input = evaluate model.base b right input := by
  induction path with
  | refl => rfl
  | step change => exact change.sound model valid left right input
  | comp first second one two =>
      let middle := (valid.restrict Finset.subset_union_left).restrict (RewriteTrack.boundaries first).2
      exact (one (valid.restrict Finset.subset_union_left) left middle).trans
        (two (valid.restrict Finset.subset_union_right) middle right)
  | inv child ih => exact (ih valid right left).symm

end RewriteTrack

namespace Homotopy

/-- Include intermediate comparison tracks; cancellation never silently
removes the guards used to construct the higher witness. -/
def support {n m : Port signature} : {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → Homotopy p q → Finset Requirement
  | _, _, _, _, .refl p => RewriteTrack.support p
  | _, _, _, _, .generator generator => generator.support
  | _, _, _, _, .symm cell => support cell
  | _, _, _, _, .trans first second => support first ∪ support second
  | _, _, _, _, .comp first second => support first ∪ support second
  | _, _, _, _, .inverse child => support child
  | _, _, _, _, .assoc p q r => RewriteTrack.support p ∪ RewriteTrack.support q ∪ RewriteTrack.support r
  | _, _, _, _, .leftUnit p | _, _, _, _, .rightUnit p => RewriteTrack.support p
  | _, _, _, _, .leftInv p | _, _, _, _, .rightInv p => RewriteTrack.support p

end Homotopy
namespace Exchange

theorem boundaries {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (generator : Exchange p q) : RewriteTrack.support p ⊆ generator.support ∧ RewriteTrack.support q ⊆ generator.support := by
  cases generator with
  | separated witness =>
      have covered := witness.no_new_conditions
      simp only [support, route, RewriteTrack.support, RewriteTrack.ofPath_support, Path.single_support]
      exact ⟨Finset.union_subset Finset.subset_union_left covered.1,
        Finset.union_subset Finset.subset_union_right covered.2⟩

end Exchange

namespace Homotopy

theorem boundaries {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : Homotopy p q) : RewriteTrack.support p ⊆ support cell ∧ RewriteTrack.support q ⊆ support cell := by
  induction cell with
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | generator generator => exact generator.boundaries
  | symm cell ih => exact ⟨ih.2, ih.1⟩
  | trans first second one two =>
      exact ⟨fun _ h => Finset.mem_union_left _ (one.1 h), fun _ h => Finset.mem_union_right _ (two.2 h)⟩
  | comp first second one two => exact ⟨Finset.union_subset_union one.1 two.1, Finset.union_subset_union one.2 two.2⟩
  | inverse child ih => exact ih
  | assoc p q r =>
      simp only [support, RewriteTrack.support, Finset.union_assoc]
      exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | leftUnit p =>
      exact ⟨Finset.union_subset (RewriteTrack.boundaries p).1 (Finset.Subset.refl _), Finset.Subset.refl _⟩
  | rightUnit p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (RewriteTrack.boundaries p).2, Finset.Subset.refl _⟩
  | leftInv p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _), (RewriteTrack.boundaries p).2⟩
  | rightInv p =>
      exact ⟨Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _), (RewriteTrack.boundaries p).1⟩

/-- Counts exchange generators in this produced witness, not minimal proof
size, bytes, or the cost of the proof-groupoid laws. -/
def exchangeCount {n m : Port signature} : {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → Homotopy p q → Nat
  | _, _, _, _, .generator _ => 1
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => exchangeCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => exchangeCount first + exchangeCount second
  | _, _, _, _, _ => 0

/-- Counts Four constructors only; boundary tracks, placement witnesses,
condition sets, and all their payload bytes are excluded. -/
def constructorCount {n m : Port signature} : {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → Homotopy p q → Nat
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => 1 + constructorCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => 1 + constructorCount first + constructorCount second
  | _, _, _, _, _ => 1

theorem repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators updated Value) {n m} {a b : Circuit signature n m}
    {p q : RewriteTrack (relators := relators) a b} (cell : Homotopy p q) (changed : Finset Requirement)
    (cached : Holds old (support cell)) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (support cell) changed)) :
    Holds updated (RewriteTrack.support p) ∧ Holds updated (RewriteTrack.support q) ∧
      ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
        ∀ input, evaluate model.base a left input = evaluate model.base b right input := by
  let valid := repair cached unchanged rechecked
  let first := valid.restrict cell.boundaries.1
  let second := valid.restrict cell.boundaries.2
  exact ⟨first, second, first.restrict (RewriteTrack.boundaries p).1,
    first.restrict (RewriteTrack.boundaries p).2, fun input => RewriteTrack.sound model p first _ _ input⟩

end Homotopy

namespace Placement

theorem apply_needs {a b c d} (place : Placement (signature := signature) a b c d) (circuit : Circuit signature a b) :
    (place.apply circuit).needs = circuit.needs ∪ place.needs := by
  cases place <;> simp only [apply, needs, Circuit.needs, Finset.union_comm]

theorem step_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} (change : Step relators x y) :
    (place.step change).support = change.support ∪ place.needs := by
  cases place <;> simp only [step, needs, Step.support, Finset.union_comm]

theorem track_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} (path : RewriteTrack (relators := relators) x y) :
    RewriteTrack.support (place.track path) = RewriteTrack.support path ∪ place.needs := by
  induction path with
  | refl => exact apply_needs place _
  | step change => exact step_support place change
  | comp first second one two =>
      simp only [track, Track.map, RewriteTrack.support] at one two ⊢
      rw [one, two]
      simp only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm, Finset.union_left_idem]
  | inv child ih => exact ih

theorem map_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} (path : RewriteTrack (relators := relators) x y) :
    RewriteTrack.support (Track.map place.apply (fun change => place.step change) path) = RewriteTrack.support path ∪ place.needs :=
  track_support place path

end Placement

namespace Exchange

theorem whisker_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y} (generator : Exchange p q) :
    (generator.whisker place).support = generator.support ∪ place.needs := by
  cases generator with
  | separated witness =>
      cases place <;> simp only [whisker, support, Step.support, Placement.needs,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm, Finset.union_left_idem]

end Exchange

namespace Homotopy

theorem whisker_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y} (cell : Homotopy p q) :
    support (cell.whisker place) = support cell ∪ place.needs := by
  induction cell with
  | refl path => exact place.track_support path
  | generator generator => exact generator.whisker_support place
  | symm cell ih | inverse cell ih => exact ih
  | trans first second one two | comp first second one two =>
      simp only [whisker, support, one, two, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm, Finset.union_self]
  | assoc p q r =>
      simp only [whisker, support, Placement.map_support, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm, Finset.union_left_idem]
  | leftUnit p | rightUnit p | leftInv p | rightInv p => exact place.track_support p

omit [DecidableEq Requirement] in
theorem whisker_exchangeCount {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y} (cell : Homotopy p q) :
    exchangeCount (cell.whisker place) = exchangeCount cell := by
  induction cell <;> simp_all only [whisker, exchangeCount]

omit [DecidableEq Requirement] in
theorem whisker_constructorCount {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y} (cell : Homotopy p q) :
    constructorCount (cell.whisker place) = constructorCount cell := by
  induction cell <;> simp_all only [whisker, constructorCount]

theorem whisker_fresh {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y} (cell : Homotopy p q) (changed : Finset Requirement) :
    fresh (support (cell.whisker place)) changed = fresh (support cell) changed ∪ fresh place.needs changed := by
  rw [whisker_support]
  ext label
  simp only [fresh, Finset.mem_inter, Finset.mem_union]
  tauto

end Homotopy

end CryptoLogic.Polygraph.MixedCircuit
