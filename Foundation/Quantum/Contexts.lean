import Foundation.Logic.Presentation
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-! Heunen 5.3.6: the tautological functor of commutative closed contexts.
Persistent propositions give the Kripke interpretation of propositional logic.
This is not a construction of the internal spectrum or Gelfand duality. -/
namespace Foundation.Quantum.Bohr
open CategoryTheory Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CStarAlgebra A]

structure Context where
  algebra : StarSubalgebra ℂ A
  closed : IsClosed (algebra : Set A)
  commutative : ∀ x y : algebra, x * y = y * x

instance : Preorder (Context A) where
  le C D := C.algebra ≤ D.algebra
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

/-- The context is sent to its own elements; arrows are actual inclusions. -/
def tautological : Context A ⥤ Type where
  obj C := C.algebra
  map f := TypeCat.ofHom (fun x => StarSubalgebra.inclusion (leOfHom f) x)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem local_commutativity (C : Context A) (x y : C.algebra) : x * y = y * x :=
  C.commutative x y

theorem inclusion_mul {C D : Context A} (h : C ≤ D) (x y : C.algebra) :
    StarSubalgebra.inclusion h (x * y) =
      StarSubalgebra.inclusion h x * StarSubalgebra.inclusion h y := rfl

theorem inclusion_star {C D : Context A} (h : C ≤ D) (x : C.algebra) :
    StarSubalgebra.inclusion h (star x) = star (StarSubalgebra.inclusion h x) := rfl

theorem inclusion_norm {C D : Context A} (h : C ≤ D) (x : C.algebra) :
    ‖StarSubalgebra.inclusion h x‖ = ‖x‖ := rfl

/-- Truth persists as the set of available commuting observations grows. -/
structure Persistent where
  holds : Context A → Prop
  monotone : ∀ {C D}, C ≤ D → holds C → holds D

namespace Persistent
variable {A}

def entails (P Q : Persistent A) : Prop := ∀ C, P.holds C → Q.holds C

def meet (P Q : Persistent A) : Persistent A where
  holds C := P.holds C ∧ Q.holds C
  monotone h hp := ⟨P.monotone h hp.1, Q.monotone h hp.2⟩

def imp (P Q : Persistent A) : Persistent A where
  holds C := ∀ D, C ≤ D → P.holds D → Q.holds D
  monotone h hp D hd := hp D (h.trans hd)

/-- Heyting implication quantifies over all future contexts, unlike the Sasaki hook. -/
theorem implication_adjunction (P Q R : Persistent A) :
    entails (meet P Q) R ↔ entails P (imp Q R) := by
  constructor
  · intro h C hp D hd hq
    exact h D ⟨P.monotone hd hp, hq⟩
  · intro h C hp
    exact h C hp.1 C le_rfl hp.2
end Persistent

namespace Persistent
variable {A}
def bottom : Persistent A := ⟨fun _ => False, fun _ h => h⟩
def top : Persistent A := ⟨fun _ => True, fun _ _ => trivial⟩
def join (P Q : Persistent A) : Persistent A where
  holds C := P.holds C ∨ Q.holds C
  monotone h hp := hp.elim (fun p => Or.inl (P.monotone h p))
    (fun q => Or.inr (Q.monotone h q))
def contains (x : A) : Persistent A := ⟨fun C => x ∈ C.algebra, fun h hx => h hx⟩
end Persistent

inductive Formula where
  | atom : Nat → Formula
  | bottom | top : Formula
  | join : Formula → Formula → Formula
  | meet : Formula → Formula → Formula
  | imp : Formula → Formula → Formula

inductive Rule where
  | refl (P : Formula)
  | bottom (P : Formula)
  | top (P : Formula)
  | joinLeft (P Q : Formula)
  | joinRight (P Q : Formula)
  | joinElim (P Q R : Formula)
  | trans (P Q R : Formula)
  | meetLeft (P Q : Formula)
  | meetRight (P Q : Formula)
  | meetIntro (P Q R : Formula)
  | impIntro (P Q R : Formula)
  | impElim (P Q R : Formula)

abbrev presentation : Presentation where
  Judgment := Formula × Formula
  Rule := Rule
  arity := fun | .trans .. | .meetIntro .. | .joinElim .. => 2 | .impIntro .. | .impElim .. => 1 | _ => 0
  premise := fun
    | .trans P Q R => Fin.cases (P, Q) (fun _ => (Q, R))
    | .meetIntro P Q R => Fin.cases (P, Q) (fun _ => (P, R))
    | .joinElim P Q R => Fin.cases (P, R) (fun _ => (Q, R))
    | .impIntro P Q R => fun _ => (.meet P Q, R)
    | .impElim P Q R => fun _ => (P, .imp Q R)
    | .refl _ | .bottom _ | .top _ | .joinLeft .. | .joinRight .. | .meetLeft .. | .meetRight .. => Fin.elim0
  conclusion := fun
    | .refl P => (P, P)
    | .bottom P => (.bottom, P)
    | .top P => (P, .top)
    | .joinLeft P Q => (P, .join P Q)
    | .joinRight P Q => (Q, .join P Q)
    | .joinElim P Q R => (.join P Q, R)
    | .trans P _ R => (P, R)
    | .meetLeft P Q => (.meet P Q, P)
    | .meetRight P Q => (.meet P Q, Q)
    | .meetIntro P Q R => (P, .meet Q R)
    | .impIntro P Q R => (P, .imp Q R)
    | .impElim P Q R => (.meet P Q, R)

def Formula.eval (ν : Nat → Persistent A) : Formula → Persistent A
  | .atom n => ν n
  | .bottom => Persistent.bottom
  | .top => Persistent.top
  | .join P Q => Persistent.join (P.eval ν) (Q.eval ν)
  | .meet P Q => Persistent.meet (P.eval ν) (Q.eval ν)
  | .imp P Q => Persistent.imp (P.eval ν) (Q.eval ν)

def model (ν : Nat → Persistent A) : Model presentation where
  Carrier j := Persistent.entails (j.1.eval A ν) (j.2.eval A ν)
  operation := fun r h => match r with
    | .refl _ => fun _ hp => hp
    | .bottom _ => fun _ hp => hp.elim
    | .top _ => fun _ _ => trivial
    | .joinLeft .. => fun _ hp => Or.inl hp
    | .joinRight .. => fun _ hp => Or.inr hp
    | .joinElim .. => fun C hp => hp.elim (h 0 C) (h 1 C)
    | .trans .. => fun C hp => h 1 C (h 0 C hp)
    | .meetLeft .. => fun _ hp => hp.1
    | .meetRight .. => fun _ hp => hp.2
    | .meetIntro .. => fun C hp => ⟨h 0 C hp, h 1 C hp⟩
    | .impIntro .. => (Persistent.implication_adjunction _ _ _).mp (h 0)
    | .impElim .. => (Persistent.implication_adjunction _ _ _).mpr (h 0)

theorem sound (ν : Nat → Persistent A) {Γ : Logic.Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model A ν).Carrier (Γ.claim i)) :
    (model A ν).Carrier j := d.eval (model A ν) h

theorem interpretation_substitute (ν : Nat → Persistent A)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model A ν).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model A ν) h =
      d.eval (model A ν) (fun i => (r i).eval (model A ν) h) :=
  Derivation.eval_substitute (model A ν) h d r

end
end Foundation.Quantum.Bohr
