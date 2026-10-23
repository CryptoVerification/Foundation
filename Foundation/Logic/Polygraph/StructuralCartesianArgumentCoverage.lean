import Foundation.Logic.Polygraph.StructuralCartesianNaturality
import Mathlib.Tactic.FinCases

/-! Coverage of ALL wire-argument positions of the eighteen cartesian roots.
This does not classify overlaps inside fixed structural gates of their patterns
or assert higher completeness. Shape parameters are objects, not wire arguments. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def argumentCount {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q) : Nat :=
  match root with
  | .assoc _ _ _ | .forkAfter _ _ _ => 3
  | .betaFst _ _ | .betaSnd _ _ | .tensorExpand _ _ => 2
  | .leftId _ | .rightId _ | .eta _ | .discardAfter _ => 1
  | _ => 0

structure Argument {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q) where
  input : Shape Atom
  output : Shape Atom
  value : Wire input output
  variation : Variation input output a b
  same : HEq (variation.rootAt value) root

def argumentAt : {a b : Shape Atom} → {p q : Wire a b} → (root : Cartesian.Root p q) →
    Fin (argumentCount root) → Argument root
  | _, _, _, _, .assoc p q r, index => Fin.cases ⟨_, _, p, .assocFirst q r, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, q, .assocMiddle p r, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, r, .assocLast p q, HEq.rfl⟩ Fin.elim0 rest) rest) index
  | _, _, _, _, .leftId p, index => Fin.cases ⟨_, _, p, .leftId _ _, HEq.rfl⟩ Fin.elim0 index
  | _, _, _, _, .rightId p, index => Fin.cases ⟨_, _, p, .rightId _ _, HEq.rfl⟩ Fin.elim0 index
  | _, _, _, _, .betaFst p q, index => Fin.cases ⟨_, _, p, .betaFstFirst q, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, q, .betaFstLast p, HEq.rfl⟩ Fin.elim0 rest) index
  | _, _, _, _, .betaSnd p q, index => Fin.cases ⟨_, _, p, .betaSndFirst q, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, q, .betaSndLast p, HEq.rfl⟩ Fin.elim0 rest) index
  | _, _, _, _, .eta p, index => Fin.cases ⟨_, _, p, .eta _ _ _, HEq.rfl⟩ Fin.elim0 index
  | _, _, _, _, .discardAfter p, index => Fin.cases ⟨_, _, p, .discard _ _, HEq.rfl⟩ Fin.elim0 index
  | _, _, _, _, .forkAfter p q r, index => Fin.cases ⟨_, _, p, .forkFirst q r, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, q, .forkMiddle p r, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, r, .forkLast p q, HEq.rfl⟩ Fin.elim0 rest) rest) index
  | _, _, _, _, .tensorExpand p q, index => Fin.cases ⟨_, _, p, .tensorFirst q, HEq.rfl⟩ (fun rest => Fin.cases ⟨_, _, q, .tensorLast p, HEq.rfl⟩ Fin.elim0 rest) index
  | _, _, _, _, .copyExpand _, index => Fin.elim0 index
  | _, _, _, _, .swapExpand _ _, index => Fin.elim0 index
  | _, _, _, _, .assocExpand _ _ _, index => Fin.elim0 index
  | _, _, _, _, .unassocExpand _ _ _, index => Fin.elim0 index
  | _, _, _, _, .leftUnitExpand _, index => Fin.elim0 index
  | _, _, _, _, .rightUnitExpand _, index => Fin.elim0 index
  | _, _, _, _, .leftUnitInvExpand _, index => Fin.elim0 index
  | _, _, _, _, .rightUnitInvExpand _, index => Fin.elim0 index
  | _, _, _, _, .unitIdentity, index => Fin.elim0 index

def argumentTag : {a b : Shape Atom} → {p q : Wire a b} → (root : Cartesian.Root p q) →
    Fin (argumentCount root) → Fin 16
  | _, _, _, _, .assoc _ _ _, index => ⟨0 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .leftId _, index => ⟨3 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .rightId _, index => ⟨4 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .betaFst _ _, index => ⟨5 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .betaSnd _ _, index => ⟨7 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .eta _, index => ⟨9 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .discardAfter _, index => ⟨10 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .forkAfter _ _ _, index => ⟨11 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .tensorExpand _ _, index => ⟨14 + index.val, by have bound := index.isLt; simp only [argumentCount] at bound; omega⟩
  | _, _, _, _, .copyExpand _, index => Fin.elim0 index
  | _, _, _, _, .swapExpand _ _, index => Fin.elim0 index
  | _, _, _, _, .assocExpand _ _ _, index => Fin.elim0 index
  | _, _, _, _, .unassocExpand _ _ _, index => Fin.elim0 index
  | _, _, _, _, .leftUnitExpand _, index => Fin.elim0 index
  | _, _, _, _, .rightUnitExpand _, index => Fin.elim0 index
  | _, _, _, _, .leftUnitInvExpand _, index => Fin.elim0 index
  | _, _, _, _, .rightUnitInvExpand _, index => Fin.elim0 index
  | _, _, _, _, .unitIdentity, index => Fin.elim0 index

theorem argumentAt_tag {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q)
    (index : Fin (argumentCount root)) : (argumentAt root index).variation.code = argumentTag root index := by
  cases root <;> fin_cases index <;> rfl

theorem argument_coverage {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q)
    (index : Fin (argumentCount root)) :
    Nonempty {instantiation : Argument root // instantiation.variation.code = argumentTag root index} :=
  ⟨⟨argumentAt root index, argumentAt_tag root index⟩⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
