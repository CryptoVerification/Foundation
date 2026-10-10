import Foundation.Quantum.QKD.CollisionVariance
import Foundation.Logic.Presentation

/-! A finite calculus for the operator collision step of privacy amplification.
The two-universality certificate is checked for the concrete seed distribution;
input collision bounds remain hypotheses to be proved on concrete matrices. -/
namespace Foundation.Quantum.QKD.CollisionLogic
noncomputable section
open Foundation.Logic
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | input (state : Nat) (q : ℝ)
  | variance (state : Nat) (q : ℝ)

inductive Rule where
  | hash (state : Nat) (q : ℝ)
  | weaken (state : Nat) (q r : ℝ) (h : q ≤ r)

abbrev presentation (outputCard : Nat) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun _ => 1
  premise := fun
    | .hash s q => fun _ => .input s q
    | .weaken s q _ _ => fun _ => .variance s q
  conclusion := fun
    | .hash s q => .variance s ((1 - 1 / outputCard) * q)
    | .weaken s _ r _ => .variance s r

variable {X Y S : Type} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S] {e : Space}

def model (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    Model (presentation (Fintype.card Y)) where
  Carrier := fun
    | .input s q => Collision.input (B s) ≤ q
    | .variance s q => Collision.variance p h (B s) ≤ q
  operation := fun r hs => by
    cases r with
    | hash s q =>
      apply (Collision.variance_sharp_le p h (B s) (hB s) hδ).trans
      have hc : (1:ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
      exact mul_le_mul_of_nonneg_left (hs 0) (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hc))
    | weaken s q r hqr => exact (hs 0).trans hqr

theorem sound (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (hs : ∀ i, (model p h B hB hδ).Carrier (Γ.claim i)) : (model p h B hB hδ).Carrier j := d.eval _ hs

theorem interpretation_substitute (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ Δ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (r : ∀ i, Derivation (presentation (Fintype.card Y)) Δ (Γ.claim i))
    (hs : ∀ i, (model p h B hB hδ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model p h B hB hδ) hs =
      d.eval (model p h B hB hδ) (fun i => (r i).eval (model p h B hB hδ) hs) :=
  Derivation.eval_substitute _ hs d r

/-- A two-step derivation uses the sharp coefficient and then a requested bound. -/
def proof (outputCard state : Nat) (q r : ℝ) (hr : (1 - 1 / outputCard) * q ≤ r) :
    Derivation (presentation outputCard) (Logic.Context.singleton (.input state q)) (.variance state r) :=
  .apply (T := presentation outputCard) (.weaken state _ r hr) (fun _ =>
    .apply (T := presentation outputCard) (.hash state q) (fun _ => .hypothesis 0))

end
end Foundation.Quantum.QKD.CollisionLogic
