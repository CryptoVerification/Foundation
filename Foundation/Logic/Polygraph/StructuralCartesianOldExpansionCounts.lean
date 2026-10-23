import Foundation.Logic.Polygraph.StructuralCartesianOldExpansion

/-! A uniform bound on actual new-root occurrences, including formal inverse
uses, for every contextual old step and every old proof track. Context payload
and proof/circuit bytes are excluded. No claim of forward simulation is made. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.BoundedOld
open Foundation.Logic.Polygraph
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def steps {A : Type} {R : A → A → Type} : {a b : A} → Track R a b → Nat
  | _, _, .refl _ => 0
  | _, _, .step _ => 1
  | _, _, .comp first second => steps first + steps second
  | _, _, .inv child => steps child

theorem steps_map {A B : Type} {R : A → A → Type} {S : B → B → Type}
    (f : A → B) (maps : ∀ {a b}, R a b → S (f a) (f b)) {a b : A} (path : Track R a b) :
    steps (path.map f maps) = steps path := by
  induction path <;> simp_all only [Track.map, steps]

theorem toTrack_steps {a b : Shape Atom} {p q : Wire a b} (proof : Cell p q) : steps proof.toTrack = roots proof := by
  induction proof with
  | refl => rfl
  | root => rfl
  | symm child ih => exact ih
  | trans first second one two => simp only [Cell.toTrack, steps, roots, one, two]
  | seq first second one two =>
      simp only [Cell.toTrack, steps, roots, seqLeftTrack, seqRightTrack, steps_map, one, two]
  | tensor first second one two =>
      simp only [Cell.toTrack, steps, roots, tensorLeftTrack, tensorRightTrack, steps_map, one, two]

def expandStep : {a b : Shape Atom} → {p q : Wire a b} → Rewrite.Step p q → Cell p q
  | _, _, _, _, .root root => expandRoot root
  | _, _, _, _, .seqLeft change fixed => .seq (expandStep change) (.refl fixed)
  | _, _, _, _, .seqRight fixed change => .seq (.refl fixed) (expandStep change)
  | _, _, _, _, .tensorLeft change fixed => .tensor (expandStep change) (.refl fixed)
  | _, _, _, _, .tensorRight fixed change => .tensor (.refl fixed) (expandStep change)

theorem expandStep_roots {a b : Shape Atom} {p q : Wire a b} (change : Rewrite.Step p q) :
    roots (expandStep change) ≤ 20 := by
  induction change with
  | root root => exact roots_bounded root
  | seqLeft child fixed ih | tensorLeft child fixed ih => simpa only [expandStep, roots, Nat.add_zero] using ih
  | seqRight fixed child ih | tensorRight fixed child ih => simpa only [expandStep, roots, Nat.zero_add] using ih

theorem expandStep_steps {a b : Shape Atom} {p q : Wire a b} (change : Rewrite.Step p q) :
    steps (expandStep change).toTrack ≤ 20 := by rw [toTrack_steps]; exact expandStep_roots change

def expandTrack {a b : Shape Atom} : {p q : Wire a b} → Track (fun x y => Rewrite.Step x y) p q → ProofTrack p q
  | _, _, .refl p => .refl p
  | _, _, .step change => (expandStep change).toTrack
  | _, _, .comp first second => .comp (expandTrack first) (expandTrack second)
  | _, _, .inv child => .inv (expandTrack child)

theorem expandTrack_steps {a b : Shape Atom} {p q : Wire a b} (path : Track (fun x y => Rewrite.Step x y) p q) :
    steps (expandTrack path) ≤ 20 * steps path := by
  induction path with
  | refl => exact Nat.le_refl 0
  | step change => simpa only [expandTrack, steps, Nat.mul_one] using expandStep_steps change
  | comp first second one two =>
      simp only [expandTrack, steps, Nat.mul_add]
      exact Nat.add_le_add one two
  | inv child ih => exact ih

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.BoundedOld
