import Foundation.Logic.Presentation
import Foundation.Quantum.Space
import Mathlib.Data.Real.Basic

/-! A finite proof calculus for operational error bounds. Gate assignments and
probabilities do not occur in the rules. -/
namespace Foundation.Quantum.Security
open Foundation.Logic

inductive Term : Space → Space → Type where
  | variable (a : Space) (label : Nat) : Term a a
  | identity (a) : Term a a
  | mix : Term .bit .bit
  | otpAverage : Term .bit .bit
  | otpIdeal : Term .bit .bit
  | dephase (a) : Term a a
  | seq {a b c} : Term a b → Term b c → Term a c

structure Claim where
  source : Space
  target : Space
  left : Term source target
  right : Term source target
  error : ℝ

abbrev claim {a b} (f g : Term a b) (ε : ℝ) : Claim := ⟨a, b, f, g, ε⟩

inductive Rule where
  | refl {a b} (f : Term a b)
  | symm {a b} (f g : Term a b) (ε : ℝ)
  | trans {a b} (f g h : Term a b) (ε δ : ℝ)
  | seq {a b c} (f f' : Term a b) (g g' : Term b c) (ε δ : ℝ)
  | weaken {a b} (f g : Term a b) (ε δ : ℝ) (bound : ε ≤ δ)
  | dephaseIdem (a : Space)
  | otpPrivacy

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .refl _ | .dephaseIdem _ | .otpPrivacy => 0 | .trans .. | .seq .. => 2 | _ => 1
  premise := fun
    | .refl _ | .dephaseIdem _ | .otpPrivacy => Fin.elim0
    | .symm f g ε | .weaken f g ε _ _ => fun _ => claim f g ε
    | .trans f g h ε δ => Fin.cases (claim f g ε) (fun _ => claim g h δ)
    | .seq f f' g g' ε δ => Fin.cases (claim f f' ε) (fun _ => claim g g' δ)
  conclusion := fun
    | .refl f => claim f f 0
    | .symm f g ε => claim g f ε
    | .trans f _ h ε δ => claim f h (ε + δ)
    | .seq f f' g g' ε δ => claim (.seq f g) (.seq f' g') (ε + δ)
    | .weaken f g _ δ _ => claim f g δ
    | .dephaseIdem a => claim (.seq (.dephase a) (.dephase a)) (.dephase a) 0
    | .otpPrivacy => claim .otpAverage .otpIdeal 0

abbrev Proof (Γ : Context presentation) {a b} (f g : Term a b) (ε : ℝ) :=
  Derivation presentation Γ (claim f g ε)

namespace Proof
variable {Γ : Context presentation} {a b c : Space}

def refl (f : Term a b) : Proof Γ f f 0 :=
  .apply (T := presentation) (.refl f) (fun i => Fin.elim0 i)

def trans {f g h : Term a b} {ε δ : ℝ} (p : Proof Γ f g ε) (q : Proof Γ g h δ) :
    Proof Γ f h (ε + δ) :=
  .apply (T := presentation) (.trans f g h ε δ) (Fin.cases p (fun _ => q))

def seq {f f' : Term a b} {g g' : Term b c} {ε δ : ℝ}
    (p : Proof Γ f f' ε) (q : Proof Γ g g' δ) :
    Proof Γ (.seq f g) (.seq f' g') (ε + δ) :=
  .apply (T := presentation) (.seq f f' g g' ε δ) (Fin.cases p (fun _ => q))

def dephaseIdem (a : Space) : Proof Γ (.seq (.dephase a) (.dephase a)) (.dephase a) 0 :=
  .apply (T := presentation) (.dephaseIdem a) (fun i => Fin.elim0 i)
def otpPrivacy : Proof Γ .otpAverage .otpIdeal 0 :=
  .apply (T := presentation) .otpPrivacy (fun i => Fin.elim0 i)
end Proof

/-- Replacing both stages of a two-stage experiment adds the two explicit errors. -/
def twoStage {a b c} (f f' : Term a b) (g g' : Term b c) (ε δ : ℝ) :
    Proof (⟨2, Fin.cases (claim f f' ε) (fun _ => claim g g' δ)⟩) (.seq f g) (.seq f' g') (ε + δ) :=
  Proof.seq (.hypothesis 0) (.hypothesis 1)

end Foundation.Quantum.Security
