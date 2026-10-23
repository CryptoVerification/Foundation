import Foundation.Logic.Polygraph.StructuralCartesianOneHole

/-! Two explicit local product critical diagrams extend the categorical
basis: projecting eta, in either component. The fork/eta triangle is derived
in StructuralCartesianProductTriangleCoherence. Each new boundary is one step. This is
not a whole-normalization generator or a complete Cartesian coherence basis. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def etaFst {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    ProofTrack (.seq (fork (.seq p (fst b c)) (.seq p (snd b c))) (fst b c)) (.seq p (fst b c)) :=
  .step (.seqLeft (.root (.eta p)) (fst b c))

def betaEtaFst {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    ProofTrack (.seq (fork (.seq p (fst b c)) (.seq p (snd b c))) (fst b c)) (.seq p (fst b c)) :=
  .step (.root (.betaFst (.seq p (fst b c)) (.seq p (snd b c))))

def etaSnd {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    ProofTrack (.seq (fork (.seq p (fst b c)) (.seq p (snd b c))) (snd b c)) (.seq p (snd b c)) :=
  .step (.seqLeft (.root (.eta p)) (snd b c))

def betaEtaSnd {a b c : Shape Atom} (p : Wire a (.pair b c)) :
    ProofTrack (.seq (fork (.seq p (fst b c)) (.seq p (snd b c))) (snd b c)) (.seq p (snd b c)) :=
  .step (.root (.betaSnd (.seq p (fst b c)) (.seq p (snd b c))))

def forkFirst {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Step.seqRight (.copy a)
    (Step.tensorLeft (Step.root (Root.betaFst p q)) (.seq (fork p q) (snd b c)))

def forkLast {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Step.seqRight (.copy a)
    (Step.tensorRight p (Step.root (Root.betaSnd p q)))

def forkBeta {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp (.step (forkFirst p q)) (.step (forkLast p q))

def forkEta {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.step (Step.root (Root.eta (fork p q)))

def forkLastFirst {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp
    (.step (Step.seqRight (.copy a) (.tensorRight (.seq (fork p q) (fst b c)) (.root (.betaSnd p q)))))
    (.step (Step.seqRight (.copy a) (.tensorLeft (.root (.betaFst p q)) q)))

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | existing {a b} {p q : Wire a b} {first second : ProofTrack p q}
      (old : CategoryCritical.Generator first second) : Generator first second
  | fst {a b c} (p : Wire a (.pair b c)) : Generator (etaFst p) (betaEtaFst p)
  | snd {a b c} (p : Wire a (.pair b c)) : Generator (etaSnd p) (betaEtaSnd p)
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Fin 25
  | _, _, _, _, _, _, .existing old => Fin.castAdd 2 old.code
  | _, _, _, _, _, _, .fst _ => ⟨23, by decide⟩
  | _, _, _, _, _, _, .snd _ => ⟨24, by decide⟩
  | _, _, _, _, _, _, .placed _ child => child.code

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 3 ∧ stepCount second ≤ 3 := by
  induction generator with
  | existing old => exact old.boundaries_bounded
  | fst | snd => change 1 ≤ 3 ∧ 1 ≤ 3; decide
  | placed place child ih => simpa only [Placement.track_count] using ih

theorem Generator.new_boundaries_single {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : 23 ≤ generator.code.val → stepCount first = 1 ∧ stepCount second = 1 := by
  induction generator with
  | existing old =>
      intro member
      change 23 ≤ old.code.val at member
      have bound := old.code.isLt
      omega
  | fst | snd => intro _; exact ⟨rfl, rfl⟩
  | placed place child ih =>
      intro member
      simpa only [Placement.track_count] using ih member

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def embed {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    CategoryCritical.Cell first second → Cell first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator old => .generator (.existing old)
  | _, _, _, _, .symm child => (embed child).symm
  | _, _, _, _, .trans first second => (embed first).trans (embed second)
  | _, _, _, _, .comp first second => .comp (embed first) (embed second)
  | _, _, _, _, .inverse child => .inverse (embed child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

def whisker {a b c d : Shape Atom} (place : Placement a b c d) : {p q : Wire a b} →
    {first second : ProofTrack p q} → Cell first second → Cell (place.track first) (place.track second)
  | _, _, _, _, .refl path => .refl _
  | _, _, _, _, .generator g => .generator (.placed place g)
  | _, _, _, _, .symm child => (whisker place child).symm
  | _, _, _, _, .trans first second => (whisker place first).trans (whisker place second)
  | _, _, _, _, .comp first second => .comp (whisker place first) (whisker place second)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc p q r => .assoc _ _ _
  | _, _, _, _, .leftUnit path => .leftUnit _
  | _, _, _, _, .rightUnit path => .rightUnit _
  | _, _, _, _, .leftInv path => .leftInv _
  | _, _, _, _, .rightInv path => .rightInv _

def fstCell {a b c : Shape Atom} (p : Wire a (.pair b c)) : Cell (etaFst p) (betaEtaFst p) := .generator (.fst p)
def sndCell {a b c : Shape Atom} (p : Wire a (.pair b c)) : Cell (etaSnd p) (betaEtaSnd p) := .generator (.snd p)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
