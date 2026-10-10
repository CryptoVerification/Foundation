import Foundation.Quantum.StateDistance
import Foundation.Quantum.OneTimePad
import Foundation.Crypto.Semantics.Probability.Comp
import Foundation.Logic.Presentation

/-! A finite proof calculus for approximate joint states, physical processing,
and finite randomized mixtures. This independent design supplies error
composition; no ideal-key premise is discharged by definition. -/
namespace Foundation.Quantum.StateDistanceLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Term where
  | state : Nat → Term
  | process : Nat → Term → Term
  | mixture (n : Nat) (p : PMF (Fin n)) (t : Fin n → Term) : Term

structure Claim where
  left : Term
  right : Term
  error : ℝ

inductive Rule where
  | refl : Term → Rule
  | symm : Term → Term → ℝ → Rule
  | trans : Term → Term → Term → ℝ → ℝ → Rule
  | post : Nat → Term → Term → ℝ → Rule
  | mixture (n : Nat) (p : PMF (Fin n)) (t u : Fin n → Term) (ε : Fin n → ℝ) : Rule
  | weaken (t u : Term) (ε δ : ℝ) (h : ε ≤ δ) : Rule

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .refl .. => 0 | .trans .. => 2 | .mixture n .. => n | _ => 1
  premise := fun
    | .refl _ => Fin.elim0
    | .symm t u ε | .post _ t u ε | .weaken t u ε _ _ => fun _ => ⟨t,u,ε⟩
    | .trans t u v ε δ => fun i => if i = 0 then ⟨t,u,ε⟩ else ⟨u,v,δ⟩
    | .mixture _ _ t u ε => fun i => ⟨t i,u i,ε i⟩
  conclusion := fun
    | .refl t => ⟨t,t,0⟩
    | .symm t u ε => ⟨u,t,ε⟩
    | .trans t _ v ε δ => ⟨t,v,ε+δ⟩
    | .post c t u ε => ⟨.process c t,.process c u,ε⟩
    | .mixture n p t u ε => ⟨.mixture n p t,.mixture n p u,∑ i, (p i).toReal * ε i⟩
    | .weaken t u _ δ _ => ⟨t,u,δ⟩

variable {a : Space}

def Term.eval (σ : Nat → Density a) (τ : Nat → Channel a a) : Term → Density a
  | .state i => σ i
  | .process c t => (τ c).run (t.eval σ τ)
  | .mixture _ p t => Density.mixture p (fun i => (t i).eval σ τ)

def model (σ : Nat → Density a) (τ : Nat → Channel a a) : Model presentation where
  Carrier j := StateApprox (j.left.eval σ τ) (j.right.eval σ τ) j.error
  operation := fun r h => by
    cases r with
    | refl t => exact StateApprox.refl _
    | symm t u ε => exact StateApprox.symm (h 0)
    | trans t u v ε δ => exact StateApprox.trans (h 0) (h 1)
    | post c t u ε => exact StateApprox.postprocess (τ c) (h 0)
    | mixture n p t u ε => exact StateApprox.mixture p _ _ ε h
    | weaken t u ε δ hεδ => exact StateApprox.weaken (h 0) hεδ

theorem sound (σ : Nat → Density a) (τ : Nat → Channel a a)
    {Γ : Context presentation} {j} (d : Derivation presentation Γ j)
    (h : ∀ i, (model σ τ).Carrier (Γ.claim i)) : (model σ τ).Carrier j := d.eval _ h

def mixtureContext (n : Nat) (t u : Fin n → Term) (ε : Fin n → ℝ) : Context presentation :=
  ⟨n, fun i => ⟨t i,u i,ε i⟩⟩

def mixtureProof (n : Nat) (p : PMF (Fin n)) (t u : Fin n → Term) (ε : Fin n → ℝ) :
    Derivation presentation (mixtureContext n t u ε)
      ⟨.mixture n p t,.mixture n p u,∑ i, (p i).toReal * ε i⟩ :=
  .apply (T := presentation) (.mixture n p t u ε)
    (fun i => .hypothesis (T := presentation) (Γ := mixtureContext n t u ε) i)

def processedMixtureProof (n : Nat) (p : PMF (Fin n)) (t u : Fin n → Term) (ε : Fin n → ℝ) (c : Nat) :
    Derivation presentation (mixtureContext n t u ε)
      ⟨.process c (.mixture n p t),.process c (.mixture n p u),∑ i, (p i).toReal * ε i⟩ :=
  .apply (T := presentation) (.post c _ _ _) (fun _ => mixtureProof n p t u ε)

theorem interpretation_substitute (σ : Nat → Density a) (τ : Nat → Channel a a)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model σ τ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model σ τ) h =
      d.eval (model σ τ) (fun i => (r i).eval (model σ τ) h) :=
  Derivation.eval_substitute _ h d r

/-- A concrete semantic environment supplied by the already verified quantum one-time pad. -/
def padStates (e : Space) (ρ : Fin 2 → Density (.tensor .bit e)) : Nat → Density (.tensor .bit e)
  | 0 => (OneTimePad.average.amplify e).run (ρ 0)
  | 1 => (OneTimePad.average.amplify e).run (ρ 1)
  | 2 => (OneTimePad.ideal.amplify e).run (ρ 0)
  | _ => (OneTimePad.ideal.amplify e).run (ρ 1)

/-- Interprets a real mixture-and-processing derivation on nontrivial quantum states, with arbitrary finite auxiliary input. -/
theorem pad_processed_interpreted (e : Space) (ρ : Fin 2 → Density (.tensor .bit e))
    (C : Channel (.tensor .bit e) (.tensor .bit e)) :
    (model (padStates e ρ) (fun _ => C)).Carrier
      ⟨.process 0 (.mixture 2 (Foundation.Probability.uniform (Fin 2)) (fun i => .state i.val)),
       .process 0 (.mixture 2 (Foundation.Probability.uniform (Fin 2)) (fun i => .state (i.val+2))),0⟩ := by
  have h := sound (padStates e ρ) (fun _ => C)
    (processedMixtureProof 2 (Foundation.Probability.uniform (Fin 2))
      (fun i => .state i.val) (fun i => .state (i.val+2)) (fun _ => 0) 0)
  simp only [mul_zero, Finset.sum_const_zero] at h
  apply h
  intro i
  fin_cases i <;> exact StateApprox.of_channel OneTimePad.perfect_privacy e (ρ _)

end
end Foundation.Quantum.StateDistanceLogic
