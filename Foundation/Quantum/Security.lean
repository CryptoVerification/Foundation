import Foundation.Quantum.SecuritySyntax
import Foundation.Quantum.OneTimePad

namespace Foundation.Quantum.Security
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Assignment := (a : Space) → Nat → Channel a a

def Term.eval (σ : Assignment) : {a b : Space} → Term a b → Channel a b
  | _, _, .variable a n => σ a n
  | _, _, .identity a => Channel.identity a
  | _, _, .mix => mixChannel
  | _, _, .otpAverage => OneTimePad.average
  | _, _, .otpIdeal => OneTimePad.ideal
  | _, _, .dephase a => Quantum.dephase a
  | _, _, .seq f g => (f.eval σ).seq (g.eval σ)

def Claim.Valid (σ : Assignment) (j : Claim) : Prop :=
  Approx (j.left.eval σ) (j.right.eval σ) j.error

def model (σ : Assignment) : Model presentation where
  Carrier := Claim.Valid σ
  operation := fun rule h => match rule with
    | .refl _ => Approx.refl _
    | .symm _ _ _ => Approx.symm (h 0)
    | .trans .. => Approx.trans (h 0) (h 1)
    | .seq .. => Approx.seq (h 0) (h 1)
    | .weaken _ _ _ _ bound => Approx.mono (h 0) bound
    | .dephaseIdem a => dephase_idempotent a
    | .otpPrivacy => OneTimePad.perfect_privacy

theorem sound (σ : Assignment) {Γ : Context presentation} {j : Claim}
    (d : Derivation presentation Γ j) (h : ∀ i, (Γ.claim i).Valid σ) : j.Valid σ :=
  d.eval (model σ) h

theorem interpretation_substitute (σ : Assignment) {Γ Δ : Context presentation} {j : Claim}
    (d : Derivation presentation Γ j) (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (Δ.claim i).Valid σ) :
    (d.substitute r).eval (model σ) h =
      d.eval (model σ) (fun i => (r i).eval (model σ) h) :=
  Derivation.eval_substitute (model σ) h d r

end
end Foundation.Quantum.Security
