import Foundation.Quantum.Infinite
import Foundation.Logic.Presentation

/-! Finite derivations interpreted by closed subspaces of an arbitrary Hilbert
space. Existential transport is closure of image; substitution is continuous preimage. -/
namespace Foundation.Quantum.InfiniteLogic
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Formula where
  | atom : Nat → Formula
  | existsAlong : Nat → Formula → Formula
  | pull : Nat → Formula → Formula

inductive Rule where
  | refl (P : Formula)
  | trans (P Q R : Formula)
  | existsIntro (f : Nat) (P Q : Formula)
  | existsElim (f : Nat) (P Q : Formula)

abbrev presentation : Presentation where
  Judgment := Formula × Formula
  Rule := Rule
  arity := fun | .refl _ => 0 | .trans .. => 2 | _ => 1
  premise := fun
    | .refl _ => Fin.elim0
    | .trans P Q R => Fin.cases (P, Q) (fun _ => (Q, R))
    | .existsIntro f P Q => fun _ => (P, .pull f Q)
    | .existsElim f P Q => fun _ => (.existsAlong f P, Q)
  conclusion := fun
    | .refl P => (P, P)
    | .trans P _ R => (P, R)
    | .existsIntro f P Q => (.existsAlong f P, Q)
    | .existsElim f P Q => (P, .pull f Q)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def Formula.eval (σ : Nat → E →L[ℂ] E) (ν : Nat → Infinite.Pred E) : Formula → Infinite.Pred E
  | .atom n => ν n
  | .existsAlong f P => (P.eval σ ν).map (σ f)
  | .pull f P => (P.eval σ ν).comap (σ f)

def model (σ : Nat → E →L[ℂ] E) (ν : Nat → Infinite.Pred E) : Model presentation where
  Carrier j := j.1.eval E σ ν ≤ j.2.eval E σ ν
  operation := fun r h => match r with
    | .refl _ => le_rfl
    | .trans .. => (h 0).trans (h 1)
    | .existsIntro .. => (ClosedSubmodule.map_le_iff_le_comap).mpr (h 0)
    | .existsElim .. => (ClosedSubmodule.map_le_iff_le_comap).mp (h 0)

theorem sound (σ : Nat → E →L[ℂ] E) (ν : Nat → Infinite.Pred E)
    {Γ : Context presentation} {j} (d : Derivation presentation Γ j)
    (h : ∀ i, (model E σ ν).Carrier (Γ.claim i)) : (model E σ ν).Carrier j :=
  d.eval (model E σ ν) h

theorem interpretation_substitute (σ : Nat → E →L[ℂ] E) (ν : Nat → Infinite.Pred E)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model E σ ν).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model E σ ν) h =
      d.eval (model E σ ν) (fun i => (r i).eval (model E σ ν) h) :=
  Derivation.eval_substitute (model E σ ν) h d r

/-- A closed derivation of the unit of existential transport. -/
def transportUnit (f : Nat) (P : Formula) : Derivation presentation (Context.empty presentation)
    (P, .pull f (.existsAlong f P)) :=
  .apply (T := presentation) (.existsElim f P (.existsAlong f P)) (fun _ =>
    .apply (T := presentation) (.refl (.existsAlong f P)) (fun i => Fin.elim0 i))

/-- The derivation has an actual infinite-dimensional interpretation. -/
theorem sequence_transport (f : Infinite.SequenceSpace →L[ℂ] Infinite.SequenceSpace)
    (P : Infinite.Pred Infinite.SequenceSpace) : P ≤ (P.map f).comap f :=
  sound Infinite.SequenceSpace (fun _ => f) (fun _ => P)
    (transportUnit 0 (.atom 0)) (fun i => Fin.elim0 i)

end
end Foundation.Quantum.InfiniteLogic
