import Foundation.Quantum.QKD.KeyVerification
import Foundation.Logic.Presentation

/-! A finite verification derivation. Its rules are the universal event bound,
fresh-hash verification and numerical weakening, not arbitrary semantic truth.
This object calculus is an implementation design, not a quoted proof system. -/
namespace Foundation.Quantum.QKD.KeyVerificationLogic
noncomputable section
open Foundation.Logic Subnormalized
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | input (state : Nat) (δ : ℝ)
  | checked (state : Nat) (δ : ℝ)

inductive Rule where
  | bounded (state : Nat)
  | verify (state : Nat) (δ : ℝ)
  | weaken (state : Nat) (δ η : ℝ) (h : δ ≤ η)

abbrev presentation (κ : ℝ) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .bounded .. => 0 | _ => 1
  premise := fun
    | .bounded .. => Fin.elim0
    | .verify s δ => fun _ => .input s δ
    | .weaken s δ _ _ => fun _ => .checked s δ
  conclusion := fun
    | .bounded s => .input s 1
    | .verify s δ => .checked s (κ*δ)
    | .weaken s _ η _ => .checked s η

variable {K T S V : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype V]
    [DecidableEq K] [DecidableEq T] [DecidableEq S] [DecidableEq V] {e : Space}

def model (ρ : Nat → State (KeyVerification.Input K T) e) (p : PMF S)
    (hash : S → K → V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hc : ∀ a b, a ≠ b → Collision.collision p hash a b ≤ κ) : Model (presentation κ) where
  Carrier := fun
    | .input s δ => CommonKey.correctnessError (ρ s) ≤ δ
    | .checked s δ => CommonKey.correctnessError (KeyVerification.accepted (ρ s) p hash) ≤ δ
  operation := fun r hs => by
    cases r with
    | bounded s => exact (KeyVerification.input_correctness_le_mass (ρ s)).trans (ρ s).bounded
    | verify s δ =>
        exact (KeyVerification.correctness_le (ρ s) p hash κ hc).trans
          (mul_le_mul_of_nonneg_left (hs 0) hκ)
    | weaken s δ η h => exact (hs 0).trans h

theorem sound (ρ : Nat → State (KeyVerification.Input K T) e) (p : PMF S)
    (hash : S → K → V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hc : ∀ a b, a ≠ b → Collision.collision p hash a b ≤ κ)
    {Γ : Logic.Context (presentation κ)} {j} (d : Derivation (presentation κ) Γ j)
    (hs : ∀ i, (model ρ p hash κ hκ hc).Carrier (Γ.claim i)) :
    (model ρ p hash κ hκ hc).Carrier j := d.eval _ hs

theorem interpretation_substitute (ρ : Nat → State (KeyVerification.Input K T) e) (p : PMF S)
    (hash : S → K → V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hc : ∀ a b, a ≠ b → Collision.collision p hash a b ≤ κ)
    {Γ Δ : Logic.Context (presentation κ)} {j} (d : Derivation (presentation κ) Γ j)
    (f : ∀ i, Derivation (presentation κ) Δ (Γ.claim i))
    (hs : ∀ i, (model ρ p hash κ hκ hc).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model ρ p hash κ hκ hc) hs =
      d.eval (model ρ p hash κ hκ hc) (fun i => (f i).eval (model ρ p hash κ hκ hc) hs) :=
  Derivation.eval_substitute _ hs d f

def proof (κ : ℝ) (s : Nat) :
    Derivation (presentation κ) (Logic.Context.empty (presentation κ)) (.checked s κ) := by
  have h : Derivation (presentation κ) (Logic.Context.empty (presentation κ)) (.checked s (κ*1)) :=
    .apply (T := presentation κ) (.verify s 1) (fun _ =>
      .apply (T := presentation κ) (.bounded s) (fun i => Fin.elim0 i))
  simpa only [mul_one] using h

end
end Foundation.Quantum.QKD.KeyVerificationLogic
