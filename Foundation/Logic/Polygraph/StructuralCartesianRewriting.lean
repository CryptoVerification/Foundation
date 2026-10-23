import Foundation.Logic.Polygraph.StructuralCartesianNormalization
import Foundation.Logic.Polygraph.StructuralWireRewrite
import Foundation.Logic.Polygraph.Rewriting

/-! Actual contextual steps for the eighteen roots, proof-track compilation,
finite typed routing decision, and a certified gap in the older eleven roots.
This is first-level equational completeness, not a finite higher coherence. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian
open TypedRouting
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Step : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | root {a b} {p q : Wire a b} : Root p q → Step p q
  | seqLeft {a b c} {p p' : Wire a b} : Step p p' → (q : Wire b c) → Step (.seq p q) (.seq p' q)
  | seqRight {a b c} (p : Wire a b) {q q' : Wire b c} : Step q q' → Step (.seq p q) (.seq p q')
  | tensorLeft {a b c d} {p p' : Wire a b} : Step p p' → (q : Wire c d) → Step (.tensor p q) (.tensor p' q)
  | tensorRight {a b c d} (p : Wire a b) {q q' : Wire c d} : Step q q' → Step (.tensor p q) (.tensor p q')

theorem Step.sound {a b} {p q : Wire (Atom := Atom) a b} (change : Step p q) (family : Atom → Type) (value : a.Value family) :
    p.eval family value = q.eval family value := by
  induction change with
  | root root => exact root.sound family value
  | seqLeft child fixed ih => exact congrArg (fixed.eval family) (ih value)
  | seqRight fixed child ih => exact ih (fixed.eval family value)
  | tensorLeft child fixed ih => exact congrArg (fun x => (x, fixed.eval family value.2)) (ih value.1)
  | tensorRight fixed child ih => exact congrArg (fun x => (fixed.eval family value.1, x)) (ih value.2)

abbrev ProofTrack {a b : Shape Atom} (p q : Wire a b) := Track (fun x y => Step x y) p q

def seqLeftTrack {a b c : Shape Atom} {p p' : Wire a b} (q : Wire b c) (path : ProofTrack p p') : ProofTrack (.seq p q) (.seq p' q) :=
  path.map (fun x => Wire.seq x q) (fun child => Step.seqLeft child q)
def seqRightTrack {a b c : Shape Atom} (p : Wire a b) {q q' : Wire b c} (path : ProofTrack q q') : ProofTrack (.seq p q) (.seq p q') :=
  path.map (fun x => Wire.seq p x) (fun child => Step.seqRight p child)
def tensorLeftTrack {a b c d : Shape Atom} {p p' : Wire a b} (q : Wire c d) (path : ProofTrack p p') : ProofTrack (.tensor p q) (.tensor p' q) :=
  path.map (fun x => Wire.tensor x q) (fun child => Step.tensorLeft child q)
def tensorRightTrack {a b c d : Shape Atom} (p : Wire a b) {q q' : Wire c d} (path : ProofTrack q q') : ProofTrack (.tensor p q) (.tensor p q') :=
  path.map (fun x => Wire.tensor p x) (fun child => Step.tensorRight p child)

def Cell.toTrack : {a b : Shape Atom} → {p q : Wire a b} → Cell p q → ProofTrack p q
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .symm child => .inv child.toTrack
  | _, _, _, _, .trans first second => .comp first.toTrack second.toTrack
  | _, _, _, _, .seq (p' := p') (q := q) first second => .comp (seqLeftTrack q first.toTrack) (seqRightTrack p' second.toTrack)
  | _, _, _, _, .tensor (p' := p') (q := q) first second => .comp (tensorLeftTrack q first.toTrack) (tensorRightTrack p' second.toTrack)
  | _, _, _, _, .root change => .step (Step.root change)

def fromOldRoot {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) : Cell p q :=
  connect p q ((normal_complete p q).mpr root.sound)

def layoutDecEq [DecidableEq Atom] (a : Shape Atom) : (b : Shape Atom) → DecidableEq (Layout a b)
  | .atom name => by
      change DecidableEq (Slot a name)
      infer_instance
  | .unit => by
      change DecidableEq PUnit
      infer_instance
  | .pair b c => by
      change DecidableEq (Layout a b × Layout a c)
      letI := layoutDecEq a b
      letI := layoutDecEq a c
      exact inferInstance

def equivalent [DecidableEq Atom] {a b : Shape Atom} (p q : Wire a b) : Bool :=
  letI := layoutDecEq a b
  decide (normal p = normal q)

theorem equivalent_correct [DecidableEq Atom] {a b : Shape Atom} (p q : Wire a b) :
    equivalent p q = true ↔ ∀ (family : Atom → Type) (value : a.Value family), p.eval family value = q.eval family value := by
  let := layoutDecEq a b
  change decide (normal p = normal q) = true ↔ _
  rw [decide_eq_true_eq]
  exact normal_complete p q

def certify [DecidableEq Atom] {a b : Shape Atom} (p q : Wire a b) : Option (Cell p q) :=
  letI := layoutDecEq a b
  if same : normal p = normal q then some (connect p q same) else none

theorem certify_complete [DecidableEq Atom] {a b : Shape Atom} (p q : Wire a b) :
    (certify p q).isSome = true ↔ Nonempty (Cell p q) := by
  let := layoutDecEq a b
  rw [complete, ← normal_complete]
  simp [certify]

def leftUnitInvCount : {a b : Shape Atom} → Wire a b → Nat
  | _, _, .seq p q | _, _, .tensor p q => leftUnitInvCount p + leftUnitInvCount q
  | _, _, .leftUnitInv _ => 1
  | _, _, _ => 0

theorem oldRoot_count {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) : leftUnitInvCount p = leftUnitInvCount q := by
  cases root <;> simp only [leftUnitInvCount] <;> omega

theorem oldStep_count {a b : Shape Atom} {p q : Wire a b} (change : Rewrite.Step p q) : leftUnitInvCount p = leftUnitInvCount q := by
  induction change with
  | root root => exact oldRoot_count root
  | seqLeft child fixed ih | tensorLeft child fixed ih => exact congrArg (fun x => x + leftUnitInvCount fixed) ih
  | seqRight fixed child ih | tensorRight fixed child ih => exact congrArg (fun x => leftUnitInvCount fixed + x) ih

theorem oldTrack_count {a b : Shape Atom} {p q : Wire a b}
    (path : Track (fun x y => Rewrite.Step x y) p q) : leftUnitInvCount p = leftUnitInvCount q := by
  induction path with
  | refl => rfl
  | step change => exact oldStep_count change
  | comp first second one two => exact one.trans two
  | inv child ih => exact ih.symm

theorem old_leftUnit_inverse_missing (a : Shape Atom) :
    ¬ Nonempty (Track (fun x y => Rewrite.Step x y) (.seq (.leftUnitInv a) (.leftUnit a)) (.identity a)) := by
  rintro ⟨path⟩
  have equality := oldTrack_count path
  change 1 + 0 = 0 at equality
  omega

def leftUnit_inverse (a : Shape Atom) : Cell (.seq (.leftUnitInv a) (.leftUnit a)) (.identity a) :=
  connect _ _ ((normal_complete _ _).mpr (fun _ _ => rfl))

/-- Unrestricted forward application is different from the derived
normalization algorithm: copy expansion can continue inside its own macro. -/
def copyChain (a : Shape Atom) : Nat → Wire a (.pair a a)
  | 0 => .copy a
  | n + 1 => .seq (copyChain a n) (.tensor (.identity a) (.identity a))

def copyChainStep (a : Shape Atom) : (n : Nat) → Step (copyChain a n) (copyChain a (n + 1))
  | 0 => .root (.copyExpand a)
  | n + 1 => .seqLeft (copyChainStep a n) _

theorem unrestricted_not_terminating (a : Shape Atom) :
    ¬ WellFounded (fun q p : Wire a (.pair a a) => Nonempty (Step p q)) := by
  intro wellFounded
  have impossible : ∀ (p : Wire a (.pair a a)),
      Acc (fun q p => Nonempty (Step p q)) p → ∀ n, p = copyChain a n → False := by
    intro p accessible
    induction accessible with
    | intro p predecessors ih =>
        intro n same
        subst p
        exact ih _ ⟨copyChainStep a n⟩ (n + 1) rfl
  exact impossible _ (wellFounded.apply _) 0 rfl

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian
