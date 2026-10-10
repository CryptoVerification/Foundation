import Foundation.Quantum.OperatorDistance
import Foundation.Logic.Presentation

/-! From explicit matrix reconstruction and collision certificates to binary
observation bounds, with physical postprocessing and error composition. These
are independently designed finite rules in the existing meta-logic. -/
namespace Foundation.Quantum.OperatorDistanceLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Term where
  | state (index : Nat)
  | process (channel : Nat) (state : Term)

inductive Claim where
  | factor (left right : Term) (witness : Nat)
  | square (witness : Nat) (q : ℝ)
  | approx (left right : Term) (error : ℝ)

inductive Rule where
  | weighted (left right : Term) (witness : Nat) (q : ℝ)
  | refl (t : Term)
  | symm (left right : Term) (error : ℝ)
  | trans (left middle right : Term) (error₁ error₂ : ℝ)
  | post (channel : Nat) (left right : Term) (error : ℝ)
  | weaken (left right : Term) (ε δ : ℝ) (h : ε ≤ δ)

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .weighted .. | .trans .. => 2 | .refl .. => 0 | _ => 1
  premise := fun
    | .weighted t u w q => fun i => if i = 0 then .factor t u w else .square w q
    | .refl _ => Fin.elim0
    | .symm t u ε | .post _ t u ε | .weaken t u ε _ _ => fun _ => .approx t u ε
    | .trans t u v ε δ => fun i => if i = 0 then .approx t u ε else .approx u v δ
  conclusion := fun
    | .weighted t u _ q => .approx t u ((1/2:ℝ)*Real.sqrt q)
    | .refl t => .approx t t 0
    | .symm t u ε => .approx u t ε
    | .trans t _ v ε δ => .approx t v (ε+δ)
    | .post c t u ε => .approx (.process c t) (.process c u) ε
    | .weaken t u _ δ _ => .approx t u δ

variable {a : Space}

def Term.eval (ρ : Nat → Operator a) (K : Nat → Channel a a) : Term → Operator a
  | .state s => ρ s
  | .process c t => (K c).toKraus.apply (t.eval ρ K)

def square (C D : Operator a) : ℝ :=
  ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re * (C*C).trace.re

def model (ρ : Nat → Operator a) (K : Nat → Channel a a) (C D : Nat → Operator a) : Model presentation where
  Carrier := fun
    | .factor t u w => (C w).IsHermitian ∧
        t.eval ρ K - u.eval ρ K = (D w).conjTranspose*(C w)*(D w) ∧
        (t.eval ρ K).trace = (u.eval ρ K).trace
    | .square w q => square (C w) (D w) ≤ q
    | .approx t u ε => OperatorApprox (t.eval ρ K) (u.eval ρ K) ε
  operation := fun r h => by
    cases r with
    | weighted t u w q =>
      have hf := h 0
      have hs := h 1
      change (C w).IsHermitian ∧ _ ∧ _ at hf
      change square (C w) (D w) ≤ q at hs
      exact (OperatorApprox.of_factor _ _ (C w) (D w) hf.1 hf.2.1 hf.2.2).weaken
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by norm_num))
    | refl t => exact OperatorApprox.refl _
    | symm t u ε => exact (h 0).symm
    | trans t u v ε δ => exact (h 0).trans (h 1)
    | post c t u ε => exact OperatorApprox.postprocess (K c) (h 0)
    | weaken t u ε δ hεδ => exact (h 0).weaken hεδ

theorem sound (ρ : Nat → Operator a) (K : Nat → Channel a a) (C D : Nat → Operator a)
    {Γ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (h : ∀ i, (model ρ K C D).Carrier (Γ.claim i)) : (model ρ K C D).Carrier j := d.eval _ h

theorem interpretation_substitute (ρ : Nat → Operator a) (K : Nat → Channel a a) (C D : Nat → Operator a)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model ρ K C D).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model ρ K C D) h = d.eval (model ρ K C D) (fun i => (r i).eval (model ρ K C D) h) :=
  Derivation.eval_substitute _ h d r

def assumptions (t u : Term) (w : Nat) (q : ℝ) : Logic.Context presentation :=
  ⟨2,fun i => if i = 0 then .factor t u w else .square w q⟩

/-- Weighted observation, physical processing, and symmetry in one derivation. -/
def weightedPostSymm (t u : Term) (w c : Nat) (q : ℝ) :
    Derivation presentation (assumptions t u w q)
      (.approx (.process c u) (.process c t) ((1/2:ℝ)*Real.sqrt q)) := by
  apply Derivation.apply (T := presentation) (.symm _ _ _)
  intro _
  apply Derivation.apply (T := presentation) (.post c t u _)
  intro _
  apply Derivation.apply (T := presentation) (.weighted t u w q)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact .hypothesis ⟨0,by change 0 < 2; decide⟩
  · have hi1 : i = 1 := by omega
    subst i
    exact .hypothesis ⟨1,by change 1 < 2; decide⟩

end
end Foundation.Quantum.OperatorDistanceLogic
