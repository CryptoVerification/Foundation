import Foundation.Quantum.GeneralCP

/-! A finite equational calculus interpreted by general C*-algebra CP maps.
Trace preservation and normality are not hidden assumptions of this calculus. -/
namespace Foundation.Quantum.GeneralCPLogic
open Foundation.Logic
open scoped CStarAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Term where
  | variable : Nat → Term
  | identity : Term
  | seq : Term → Term → Term

inductive Rule where
  | refl (f : Term)
  | symm (f g : Term)
  | trans (f g h : Term)
  | congr (f g h k : Term)
  | assoc (f g h : Term)
  | leftUnit (f : Term)
  | rightUnit (f : Term)

abbrev presentation : Presentation where
  Judgment := Term × Term
  Rule := Rule
  arity := fun | .symm .. => 1 | .trans .. | .congr .. => 2 | _ => 0
  premise := fun
    | .symm f g => fun _ => (f, g)
    | .trans f g h => Fin.cases (f, g) (fun _ => (g, h))
    | .congr f g h k => Fin.cases (f, g) (fun _ => (h, k))
    | .refl .. | .assoc .. | .leftUnit .. | .rightUnit .. => Fin.elim0
  conclusion := fun
    | .refl f => (f, f)
    | .symm f g => (g, f)
    | .trans f _ h => (f, h)
    | .congr f g h k => (.seq f h, .seq g k)
    | .assoc f g h => (.seq (.seq f g) h, .seq f (.seq g h))
    | .leftUnit f => (.seq .identity f, f)
    | .rightUnit f => (.seq f .identity, f)

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def Term.eval (σ : Nat → A →CP A) : Term → A →CP A
  | .variable n => σ n
  | .identity => GeneralCP.identity A
  | .seq f g => GeneralCP.comp (g.eval σ) (f.eval σ)

def model (σ : Nat → A →CP A) : Model presentation where
  Carrier j := ∀ x, j.1.eval A σ x = j.2.eval A σ x
  operation := fun r h => match r with
    | .refl _ => fun _ => rfl
    | .symm .. => fun x => (h 0 x).symm
    | .trans .. => fun x => (h 0 x).trans (h 1 x)
    | .congr f g h' k => fun x => by
      change h'.eval A σ (f.eval A σ x) = k.eval A σ (g.eval A σ x)
      have hfg : f.eval A σ x = g.eval A σ x := h 0 x
      have hhk : h'.eval A σ (g.eval A σ x) = k.eval A σ (g.eval A σ x) :=
        h 1 (g.eval A σ x)
      exact (congrArg (h'.eval A σ) hfg).trans hhk
    | .assoc .. => fun _ => rfl
    | .leftUnit .. => fun _ => rfl
    | .rightUnit .. => fun _ => rfl

theorem sound (σ : Nat → A →CP A) {Γ : Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model A σ).Carrier (Γ.claim i)) :
    (model A σ).Carrier j := d.eval (model A σ) h

theorem interpretation_substitute (σ : Nat → A →CP A)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model A σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model A σ) h =
      d.eval (model A σ) (fun i => (r i).eval (model A σ) h) :=
  Derivation.eval_substitute (model A σ) h d r

end
end Foundation.Quantum.GeneralCPLogic
