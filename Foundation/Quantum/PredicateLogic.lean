import Foundation.Quantum.Predicate
import Foundation.Quantum.Semantics

/-! A reconstructed chapter-4 calculus, with operation syntax from the original
quantum presentation. Finite subspace interpretations supply the local proofs. -/
namespace Foundation.Quantum.PredicateLogic
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Formula : Space → Type where
  | atom (a : Space) (label : Nat) : Formula a
  | top (a) : Formula a
  | meet {a} : Formula a → Formula a → Formula a
  | join {a} : Formula a → Formula a → Formula a
  | orth {a} : Formula a → Formula a
  | existsAlong {a b} : Quantum.Term a b → Formula a → Formula b
  | pull {a b} : Quantum.Term a b → Formula b → Formula a
  | andThen {a} : Formula a → Formula a → Formula a
  | hook {a} : Formula a → Formula a → Formula a

structure Judgment where
  space : Space
  left : Formula space
  right : Formula space
abbrev entails {a} (P Q : Formula a) : Judgment := ⟨a, P, Q⟩

inductive Rule where
  | refl {a} (P : Formula a)
  | top {a} (P : Formula a)
  | trans {a} (P Q R : Formula a)
  | meetLeft {a} (P Q : Formula a)
  | meetRight {a} (P Q : Formula a)
  | meetIntro {a} (P Q R : Formula a)
  | joinLeft {a} (P Q : Formula a)
  | joinRight {a} (P Q : Formula a)
  | joinElim {a} (P Q R : Formula a)
  | orthomodular {a} (P Q : Formula a)
  | existsIntro {a b} (f : Quantum.Term a b) (P : Formula a) (Q : Formula b)
  | existsElim {a b} (f : Quantum.Term a b) (P : Formula a) (Q : Formula b)
  | sasakiIntro {a} (P M N : Formula a)
  | sasakiElim {a} (P M N : Formula a)

abbrev presentation : Presentation where
  Judgment := Judgment
  Rule := Rule
  arity := fun
    | .trans .. | .meetIntro .. | .joinElim .. => 2
    | .orthomodular .. | .existsIntro .. | .existsElim .. | .sasakiIntro .. | .sasakiElim .. => 1
    | _ => 0
  premise := fun
    | .trans P Q R => Fin.cases (entails P Q) (fun _ => entails Q R)
    | .meetIntro P Q R => Fin.cases (entails P Q) (fun _ => entails P R)
    | .joinElim P Q R => Fin.cases (entails P R) (fun _ => entails Q R)
    | .orthomodular P Q => fun _ => entails P Q
    | .existsIntro f P Q => fun _ => entails P (.pull f Q)
    | .existsElim f P Q => fun _ => entails (.existsAlong f P) Q
    | .sasakiIntro P M N => fun _ => entails P (.hook M N)
    | .sasakiElim P M N => fun _ => entails (.andThen P M) N
    | .refl _ | .top _ | .meetLeft .. | .meetRight .. | .joinLeft .. | .joinRight .. => Fin.elim0
  conclusion := fun
    | .refl P => entails P P
    | .top P => entails P (.top _)
    | .trans P _ R => entails P R
    | .meetLeft P Q => entails (.meet P Q) P
    | .meetRight P Q => entails (.meet P Q) Q
    | .meetIntro P Q R => entails P (.meet Q R)
    | .joinLeft P Q => entails P (.join P Q)
    | .joinRight P Q => entails Q (.join P Q)
    | .joinElim P Q R => entails (.join P Q) R
    | .orthomodular P Q => entails Q (.join P (.meet (.orth P) Q))
    | .existsIntro f P Q => entails (.existsAlong f P) Q
    | .existsElim f P Q => entails P (.pull f Q)
    | .sasakiIntro P M N => entails (.andThen P M) N
    | .sasakiElim P M N => entails P (.hook M N)

abbrev Assignment := (a : Space) → Nat → Predicate.Pred a

def Formula.eval (σ : Quantum.Assignment) (ν : Assignment) : {a : Space} → Formula a → Predicate.Pred a
  | a, .atom _ n => ν a n
  | _, .top _ => ⊤
  | _, .meet P Q => P.eval σ ν ⊓ Q.eval σ ν
  | _, .join P Q => P.eval σ ν ⊔ Q.eval σ ν
  | _, .orth P => (P.eval σ ν)ᗮ
  | _, .existsAlong f P => Predicate.existsAlong (f.eval σ) (P.eval σ ν)
  | _, .pull f P => Predicate.pull (f.eval σ) (P.eval σ ν)
  | _, .andThen P M => Predicate.andThen (P.eval σ ν) (M.eval σ ν)
  | _, .hook M N => Predicate.hook (M.eval σ ν) (N.eval σ ν)

def Judgment.Valid (σ : Quantum.Assignment) (ν : Assignment) (j : Judgment) : Prop :=
  j.left.eval σ ν ≤ j.right.eval σ ν

def model (σ : Quantum.Assignment) (ν : Assignment) : Model presentation where
  Carrier := Judgment.Valid σ ν
  operation := fun r h => match r with
    | .refl _ => le_rfl
    | .top _ => le_top
    | .trans .. => (h 0).trans (h 1)
    | .meetLeft .. => inf_le_left
    | .meetRight .. => inf_le_right
    | .meetIntro .. => le_inf (h 0) (h 1)
    | .joinLeft .. => le_sup_left
    | .joinRight .. => le_sup_right
    | .joinElim .. => sup_le (h 0) (h 1)
    | .orthomodular .. => le_of_eq (Predicate.orthomodular (h 0)).symm
    | .existsIntro .. => (Predicate.exists_pull _ _ _).mpr (h 0)
    | .existsElim .. => (Predicate.exists_pull _ _ _).mp (h 0)
    | .sasakiIntro .. => (Predicate.sasaki_adjunction _ _ _).mpr (h 0)
    | .sasakiElim .. => (Predicate.sasaki_adjunction _ _ _).mp (h 0)

theorem sound (σ : Quantum.Assignment) (ν : Assignment) {Γ : Context presentation} {j : Judgment}
    (d : Derivation presentation Γ j) (h : ∀ i, (Γ.claim i).Valid σ ν) : j.Valid σ ν :=
  d.eval (model σ ν) h

theorem interpretation_substitute (σ : Quantum.Assignment) (ν : Assignment)
    {Γ Δ : Context presentation} {j : Judgment} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i)) (h : ∀ i, (Δ.claim i).Valid σ ν) :
    (d.substitute r).eval (model σ ν) h =
      d.eval (model σ ν) (fun i => (r i).eval (model σ ν) h) :=
  Derivation.eval_substitute (model σ ν) h d r

end
end Foundation.Quantum.PredicateLogic
