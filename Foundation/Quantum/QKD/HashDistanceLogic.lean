import Foundation.Quantum.QKD.HashDistance
import Foundation.Logic.Presentation

/-! Finite inference rules combining quantum collision hashing and public-seed
observation bounds. Reconstruction and numerical certificates are explicit
premises, not arbitrary semantic truth-introduction rules. -/
namespace Foundation.Quantum.QKD.HashDistanceLogic
noncomputable section
open Foundation.Logic
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | reconstruction (state witness : Nat)
  | input (state witness : Nat) (q : ℝ)
  | variance (state witness : Nat) (q : ℝ)
  | cost (witness : Nat) (r : ℝ)
  | distance (state : Nat) (ε : ℝ)

inductive Rule where
  | hash (state witness : Nat) (q : ℝ)
  | observation (state witness : Nat) (q r : ℝ)
  | weaken (state : Nat) (ε δ : ℝ) (h : ε ≤ δ)

abbrev presentation (outputCard : Nat) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .observation .. => 3 | _ => 1
  premise := fun
    | .hash s w q => fun _ => .input s w q
    | .observation s w q r => fun i => if i = 0 then .reconstruction s w else
        if i = 1 then .variance s w q else .cost w r
    | .weaken s ε _ _ => fun _ => .distance s ε
  conclusion := fun
    | .hash s w q => .variance s w ((1-1/outputCard)*q)
    | .observation s _ q r => .distance s ((1/2:ℝ)*Real.sqrt (r*q))
    | .weaken s _ δ _ => .distance s δ

variable {X Y S : Type} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S] {e : Space}

def cost (D : Operator e) : ℝ := Fintype.card Y * ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re

def model (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef) (W D : Nat → Operator e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    Model (presentation (Fintype.card Y)) where
  Carrier := fun
    | .reconstruction s w => ∀ x, B s x = (D w).conjTranspose * Collision.sandwich (W w) (B s) x * D w
    | .input s w q => Collision.input (Collision.sandwich (W w) (B s)) ≤ q
    | .variance s w q => Collision.variance p h (Collision.sandwich (W w) (B s)) ≤ q
    | .cost w r => cost (Y := Y) (D w) ≤ r
    | .distance s ε => OperatorApprox (publicMixture p (fun seed => Collision.hashed (B s) (h seed)))
        (publicMixture p (fun _ => Collision.uniformComparator (Y := Y) (B s))) ε
  operation := fun rule hs => by
    cases rule with
    | hash s w q =>
      apply (Collision.variance_sharp_le p h _ (Collision.sandwich_positive _ _ (hB s)) hδ).trans
      have hc : (1:ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
      exact mul_le_mul_of_nonneg_left (hs 0) (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hc))
    | observation s w q r =>
      have hr := hs 0
      have hq := hs 1
      have hc := hs 2
      change ∀ x, B s x = (D w).conjTranspose * Collision.sandwich (W w) (B s) x * D w at hr
      change Collision.variance p h (Collision.sandwich (W w) (B s)) ≤ q at hq
      change cost (Y := Y) (D w) ≤ r at hc
      have hc0 : 0 ≤ cost (Y := Y) (D w) := mul_nonneg (Nat.cast_nonneg _)
        (trace_square_nonneg _ (Matrix.posSemidef_self_mul_conjTranspose (D w)).isHermitian)
      apply (Collision.published_distance p h (B s) (hB s) (W w) (D w) hr).weaken
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.sqrt_le_sqrt
      exact mul_le_mul hc hq (Collision.variance_nonneg p h _ (Collision.sandwich_positive _ _ (hB s))) (hc0.trans hc)
    | weaken s ε δ hεδ => exact (hs 0).weaken hεδ

theorem sound (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef) (W D : Nat → Operator e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (hs : ∀ i, (model p h B hB W D hδ).Carrier (Γ.claim i)) : (model p h B hB W D hδ).Carrier j := d.eval _ hs

theorem interpretation_substitute (p : PMF S) (h : S → X → Y) (B : Nat → X → Operator e)
    (hB : ∀ s x, (B s x).PosSemidef) (W D : Nat → Operator e)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y)
    {Γ Δ : Logic.Context (presentation (Fintype.card Y))} {j}
    (d : Derivation (presentation (Fintype.card Y)) Γ j)
    (f : ∀ i, Derivation (presentation (Fintype.card Y)) Δ (Γ.claim i))
    (hs : ∀ i, (model p h B hB W D hδ).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model p h B hB W D hδ) hs =
      d.eval (model p h B hB W D hδ) (fun i => (f i).eval (model p h B hB W D hδ) hs) :=
  Derivation.eval_substitute _ hs d f

def assumptions (card s w : Nat) (q r : ℝ) : Logic.Context (presentation card) :=
  ⟨3,fun i => if i = 0 then .reconstruction s w else if i = 1 then .input s w q else .cost w r⟩

/-- Hashing followed by the public-seed observation rule. -/
def proof (card s w : Nat) (q r : ℝ) :
    Derivation (presentation card) (assumptions card s w q r)
      (.distance s ((1/2:ℝ)*Real.sqrt (r*((1-1/card)*q)))) := by
  apply Derivation.apply (T := presentation card) (.observation s w ((1-1/card)*q) r)
  intro i
  change Fin 3 at i
  by_cases h0 : i = 0
  · subst i
    exact .hypothesis ⟨0,by change 0 < 3; decide⟩
  · by_cases h1 : i = 1
    · subst i
      apply Derivation.apply (T := presentation card) (.hash s w q)
      intro _
      exact .hypothesis ⟨1,by change 1 < 3; decide⟩
    · have h2 : i = 2 := by omega
      subst i
      exact .hypothesis ⟨2,by change 2 < 3; decide⟩

end
end Foundation.Quantum.QKD.HashDistanceLogic
