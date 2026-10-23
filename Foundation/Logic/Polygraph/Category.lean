import Foundation.Logic.Polygraph.Cell
import Foundation.Logic.Polygraph.Higher
import Mathlib.CategoryTheory.Groupoid

/-! Strict composition on two-cells and on three-cells modulo the specified
four-dimensional presentation. The quotient of paths is not thin unless a
coherence theorem for the supplied four-generators has actually been proved. -/
namespace Foundation.Logic.Polygraph

universe j r u v w
set_option linter.checkUnivs false

instance {T : Presentation.{j, r}} : CategoryTheory.Category (Logic.Context T) where
  Hom := Cell T
  id := Cell.identity
  comp := Cell.seq
  id_comp := Cell.identity_seq
  comp_id := Cell.seq_identity
  assoc := Cell.seq_assoc

namespace Four

variable {A : Type u} {R : A → A → Type v}
  (G : {a b : A} → Track R a b → Track R a b → Type w)

def setoid (a b : A) : Setoid (Track R a b) where
  r p q := Nonempty (Four G p q)
  iseqv := ⟨fun p => ⟨.refl p⟩, fun ⟨h⟩ => ⟨.symm h⟩,
    fun ⟨h⟩ ⟨k⟩ => ⟨.trans h k⟩⟩

def Path (a b : A) := Quotient (setoid G a b)

namespace Path
variable {G} {a b c d : A}

def ofTrack (p : Track R a b) : Path G a b := Quotient.mk _ p

theorem eq_iff (p q : Track R a b) :
    ofTrack (G := G) p = ofTrack q ↔ Nonempty (Four G p q) := Quotient.eq

def identity (a : A) : Path G a a := ofTrack (.refl a)

def comp (p : Path G a b) (q : Path G b c) : Path G a c :=
  Quotient.liftOn₂ p q (fun p q => ofTrack (.comp p q))
    (fun _ _ _ _ ⟨h⟩ ⟨k⟩ => Quotient.sound ⟨Four.comp h k⟩)

def inv (p : Path G a b) : Path G b a :=
  Quotient.liftOn p (fun p => ofTrack (.inv p))
    (fun _ _ ⟨h⟩ => Quotient.sound ⟨Four.inverse h⟩)

theorem assoc (p : Path G a b) (q : Path G b c) (r : Path G c d) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        exact Quotient.sound ⟨Four.assoc p q r⟩

@[simp] theorem identity_comp (p : Path G a b) : comp (identity a) p = p := by
  induction p using Quotient.inductionOn with | _ p => exact Quotient.sound ⟨Four.leftUnit p⟩

@[simp] theorem comp_identity (p : Path G a b) : comp p (identity b) = p := by
  induction p using Quotient.inductionOn with | _ p => exact Quotient.sound ⟨Four.rightUnit p⟩

@[simp] theorem inv_comp (p : Path G a b) : comp (inv p) p = identity b := by
  induction p using Quotient.inductionOn with | _ p => exact Quotient.sound ⟨Four.leftInv p⟩

@[simp] theorem comp_inv (p : Path G a b) : comp p (inv p) = identity a := by
  induction p using Quotient.inductionOn with | _ p => exact Quotient.sound ⟨Four.rightInv p⟩

end Path

/-- A wrapper prevents unrelated four-presentations on the same vertices
from producing conflicting category instances. -/
structure Object (G : {a b : A} → Track R a b → Track R a b → Type w) where
  value : A

instance : CategoryTheory.Groupoid (Object G) where
  Hom a b := Path G a.value b.value
  id a := Path.identity a.value
  comp := Path.comp
  id_comp := Path.identity_comp
  comp_id := Path.comp_identity
  assoc := Path.assoc
  inv := Path.inv
  inv_comp := Path.inv_comp
  comp_inv := Path.comp_inv

end Four
end Foundation.Logic.Polygraph
