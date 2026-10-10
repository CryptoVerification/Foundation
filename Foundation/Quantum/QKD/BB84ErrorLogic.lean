import Foundation.Quantum.QKD.BB84FiniteError
import Foundation.Logic.Presentation

/-! A finite-error BB84 calculus with explicit measured test premises and
physical adversary postprocessing. This is an independent reconstruction,
not a calculus asserted to occur verbatim in the thesis. -/
namespace Foundation.Quantum.QKD.BB84ErrorLogic
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Processing where
  | variable : Nat → Processing
  | identity : Processing
  | seq : Processing → Processing → Processing

inductive Claim where
  | zTest : Nat → Fin 2 → ℝ → Claim
  | xPlusTest : Nat → ℝ → Claim
  | leakage : Nat → Processing → ℝ → Claim

inductive Rule where
  | tests : Nat → ℝ → ℝ → ℝ → Rule
  | post : Nat → Processing → Processing → ℝ → Rule
  | weaken (n : Nat) (t : Processing) (ε δ : ℝ) (h : ε ≤ δ)

def testClaim (n : Nat) (z0 z1 x : ℝ) (i : Fin 3) : Claim :=
  if i = 0 then .zTest n 0 z0 else if i = 1 then .zTest n 1 z1 else .xPlusTest n x

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .tests .. => 3 | .post .. | .weaken .. => 1
  premise := fun
    | .tests n z0 z1 x => testClaim n z0 z1 x
    | .post n t _ ε | .weaken n t ε _ _ => fun _ => .leakage n t ε
  conclusion := fun
    | .tests n z0 z1 x => .leakage n .identity (bb84PrivacyError z0 z1 x)
    | .post n t u ε => .leakage n (.seq t u) ε
    | .weaken n t _ δ _ => .leakage n t δ

variable {e : Space}

def Processing.eval (τ : Nat → Channel e e) : Processing → Channel e e
  | .variable n => τ n
  | .identity => Channel.identity e
  | .seq t u => (t.eval τ).seq (u.eval τ)

def meaning (σ : Nat → BB84Attack e) (τ : Nat → Channel e e) : Claim → Prop
  | .zTest n b ε => (basisEffect .bit (1 - b)).probability
      ((σ n).bobChannel.run (basisDensity .bit b)) ≤ ε
  | .xPlusTest n ε => (measurementEffect .X 1).probability
      ((σ n).bobChannel.run (prepare .X 0)) ≤ ε
  | .leakage n t ε => ∀ E : Effect e,
      |E.probability ((t.eval τ).run ((σ n).environmentState 0)) -
        E.probability ((t.eval τ).run ((σ n).environmentState 1))| ≤ ε

def model (σ : Nat → BB84Attack e) (τ : Nat → Channel e e) : Model presentation where
  Carrier := meaning σ τ
  operation := fun r h => by
    cases r with
    | tests n z0 z1 x =>
      have hz0 : (basisEffect .bit 1).probability
          ((σ n).bobChannel.run (basisDensity .bit 0)) ≤ z0 := h 0
      have hz1 : (basisEffect .bit 0).probability
          ((σ n).bobChannel.run (basisDensity .bit 1)) ≤ z1 := h 1
      intro E
      have hb := (σ n).environment_bound_of_tests hz0 hz1 (h 2) E
      simpa only [Processing.eval, Effect.probability, Channel.run, Channel.identity,
        Channel.ofIsometry, Kraus.single_apply, Matrix.one_mul, Matrix.mul_one,
        Matrix.conjTranspose_one] using hb
    | post n t u ε =>
      intro E
      have hp := h 0 ((u.eval τ).pullEffect E)
      change |((u.eval τ).pullEffect E).probability ((t.eval τ).run ((σ n).environmentState 0)) -
        ((u.eval τ).pullEffect E).probability ((t.eval τ).run ((σ n).environmentState 1))| ≤ ε at hp
      rw [← Effect.probability_run, ← Effect.probability_run] at hp
      simpa only [meaning, Processing.eval, Effect.probability, Channel.seq_run_matrix] using hp
    | weaken _ _ _ _ hεδ => intro E; exact (h 0 E).trans hεδ

theorem sound (σ : Nat → BB84Attack e) (τ : Nat → Channel e e)
    {Γ : Context presentation} {j} (d : Derivation presentation Γ j)
    (h : ∀ i, (model σ τ).Carrier (Γ.claim i)) : (model σ τ).Carrier j := d.eval (model σ τ) h

def testContext (n : Nat) (z0 z1 x : ℝ) : Context presentation :=
  ⟨3, testClaim n z0 z1 x⟩

/-- A real derivation binds the three measured error upper bounds. -/
def testProof (n : Nat) (z0 z1 x : ℝ) :
    Derivation presentation (testContext n z0 z1 x)
      (.leakage n .identity (bb84PrivacyError z0 z1 x)) :=
  .apply (T := presentation) (.tests n z0 z1 x)
    (fun i => .hypothesis (T := presentation) (Γ := testContext n z0 z1 x) i)

/-- An arbitrary adversary operation can follow the verified test inference. -/
def processedProof (n : Nat) (z0 z1 x : ℝ) (t : Processing) :
    Derivation presentation (testContext n z0 z1 x)
      (.leakage n (.seq .identity t) (bb84PrivacyError z0 z1 x)) :=
  .apply (T := presentation) (.post n .identity t _) (fun _ => testProof n z0 z1 x)

theorem interpretation_substitute (σ : Nat → BB84Attack e) (τ : Nat → Channel e e)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model σ τ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model σ τ) h =
      d.eval (model σ τ) (fun i => (r i).eval (model σ τ) h) :=
  Derivation.eval_substitute (model σ τ) h d r

end
end Foundation.Quantum.QKD.BB84ErrorLogic
