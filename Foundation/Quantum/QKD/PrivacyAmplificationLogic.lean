import Foundation.Quantum.QKD.ReferenceRegularization
import Foundation.Logic.Presentation

/-! A finite domination-to-distance calculus, valid even for singular finite
reference states. The scalar limiting argument is in the proof of rule soundness;
it does not add infinitely many premises or arbitrary truth introduction. -/
namespace Foundation.Quantum.QKD.PrivacyAmplificationLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | domination (state reference : Nat) (q : ℝ)
  | mass (state : Nat) (r : ℝ)
  | distance (state : Nat) (ε : ℝ)

inductive Rule where
  | amplify (state reference : Nat) (q r : ℝ) (hq : 0 ≤ q)
  | weaken (state : Nat) (ε δ : ℝ) (h : ε ≤ δ)

abbrev presentation (card : Nat) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .amplify .. => 2 | .weaken .. => 1
  premise := fun
    | .amplify s t q r _ => fun i => if i = 0 then .domination s t q else .mass s r
    | .weaken s ε _ _ => fun _ => .distance s ε
  conclusion := fun
    | .amplify s _ q r _ => .distance s ((1/2:ℝ)*Real.sqrt (card*((1-1/card)*(q*r))))
    | .weaken s _ δ _ => .distance s δ

variable {X Y S : Type} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S] {e : Space}

def model (p : PMF S) (h : S → X → Y) (ρ : Nat → Subnormalized.State X e) (τ : Nat → Density e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    Model (presentation (Fintype.card Y)) where
  Carrier := fun
    | .domination s t q => Subnormalized.Dominated (ρ s) (τ t) q
    | .mass s r => Subnormalized.mass (ρ s) ≤ r
    | .distance s ε => OperatorApprox (publicMixture p (fun seed => Collision.hashed (ρ s).block (h seed)))
        (publicMixture p (fun _ => Collision.uniformComparator (Y := Y) (ρ s).block)) ε
  operation := fun rule hs => by
    cases rule with
    | amplify s t q r hq =>
      apply (Collision.dominated_published_distance_general p h (ρ s) (τ t) q hq (hs 0) hδ).weaken
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hc : (1:ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hc))
      exact mul_le_mul_of_nonneg_left (hs 1) hq
    | weaken s ε δ hεδ => exact (hs 0).weaken hεδ

theorem sound (p : PMF S) (h : S → X → Y) (ρ : Nat → Subnormalized.State X e) (τ : Nat → Density e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (hs : ∀ i, (model p h ρ τ hδ).Carrier (Γ.claim i)) : (model p h ρ τ hδ).Carrier j := d.eval _ hs

theorem interpretation_substitute (p : PMF S) (h : S → X → Y) (ρ : Nat → Subnormalized.State X e)
    (τ : Nat → Density e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ Δ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (f : ∀ i, Derivation (presentation (Fintype.card Y)) Δ (Γ.claim i))
    (hs : ∀ i, (model p h ρ τ hδ).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model p h ρ τ hδ) hs =
      d.eval (model p h ρ τ hδ) (fun i => (f i).eval (model p h ρ τ hδ) hs) :=
  Derivation.eval_substitute _ hs d f

def assumptions (card s t : Nat) (q r : ℝ) : Logic.Context (presentation card) :=
  ⟨2,fun i => if i = 0 then .domination s t q else .mass s r⟩

def proof (card s t : Nat) (q r ε : ℝ) (hq : 0 ≤ q)
    (hε : (1/2:ℝ)*Real.sqrt (card*((1-1/card)*(q*r))) ≤ ε) :
    Derivation (presentation card) (assumptions card s t q r) (.distance s ε) := by
  apply Derivation.apply (T := presentation card) (.weaken s _ ε hε)
  intro _
  apply Derivation.apply (T := presentation card) (.amplify s t q r hq)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact .hypothesis ⟨0,by change 0 < 2; decide⟩
  · have hi1 : i = 1 := by omega
    subst i
    exact .hypothesis ⟨1,by change 1 < 2; decide⟩

end
end Foundation.Quantum.QKD.PrivacyAmplificationLogic
