import Foundation.Quantum.QKD.SubnormalizedGuess
import Foundation.Logic.Presentation

/-! Finite reasoning about weighted guessing bounds, branch selection and
physical quantum processing. Concrete operator/mass hypotheses are interpreted;
there is no rule admitting an arbitrary semantic statement as a theorem. -/
namespace Foundation.Quantum.QKD.SubnormalizedLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
variable (X : Type) [Fintype X]

inductive Term where
  | state (index : Nat)
  | select (state : Term) (event : Finset X)
  | process (state : Term) (channel : Nat)

inductive Claim where
  | domination (state : Term X) (reference : Nat) (q : ℝ)
  | massBound (state : Term X) (q : ℝ)
  | guessBound (state : Term X) (q : ℝ)

inductive Rule where
  | dominated (t : Term X) (reference : Nat) (q : ℝ)
  | mass (t : Term X) (q : ℝ)
  | select (t : Term X) (event : Finset X) (q : ℝ)
  | process (t : Term X) (channel : Nat) (q : ℝ)
  | weaken (t : Term X) (q r : ℝ) (h : q ≤ r)

abbrev presentation : Presentation where
  Judgment := Claim X
  Rule := Rule X
  arity := fun _ => 1
  premise := fun
    | .dominated t r q => fun _ => .domination t r q
    | .mass t q => fun _ => .massBound t q
    | .select t _ q | .process t _ q | .weaken t q _ _ => fun _ => .guessBound t q
  conclusion := fun
    | .dominated t _ q | .mass t q => .guessBound t q
    | .select t s q => .guessBound (.select t s) q
    | .process t c q => .guessBound (.process t c) q
    | .weaken t _ r _ => .guessBound t r

variable {X} [DecidableEq X] [Nonempty X] {e : Space}

def eval (ρ : Nat → Subnormalized.State X e) (C : Nat → Channel e e) : Term X → Subnormalized.State X e
  | .state s => ρ s
  | .select t s => Subnormalized.restrict (eval ρ C t) (fun x => x ∈ s)
  | .process t c => Subnormalized.post (eval ρ C t) (C c)

def model (ρ : Nat → Subnormalized.State X e) (C : Nat → Channel e e) (σ : Nat → Density e) :
    Model (presentation X) where
  Carrier := fun
    | .domination t r q => Subnormalized.Dominated (eval ρ C t) (σ r) q
    | .massBound t q => Subnormalized.mass (eval ρ C t) ≤ q
    | .guessBound t q => Subnormalized.probability (eval ρ C t) ≤ q
  operation := fun r h => by
    cases r with
    | dominated t r q => exact Subnormalized.probability_le_dominated _ _ _ (h 0)
    | mass t q => exact (Subnormalized.probability_le_mass _).trans (h 0)
    | select t s q => exact (Subnormalized.probability_restrict _ _).trans (h 0)
    | process t c q => exact (Subnormalized.probability_post _ _).trans (h 0)
    | weaken t q r hqr => exact (h 0).trans hqr

theorem sound (ρ : Nat → Subnormalized.State X e) (C : Nat → Channel e e) (σ : Nat → Density e)
    {Γ : Logic.Context (presentation X)} {j} (d : Derivation (presentation X) Γ j)
    (h : ∀ i, (model ρ C σ).Carrier (Γ.claim i)) : (model ρ C σ).Carrier j := d.eval _ h

theorem interpretation_substitute (ρ : Nat → Subnormalized.State X e) (C : Nat → Channel e e) (σ : Nat → Density e)
    {Γ Δ : Logic.Context (presentation X)} {j} (d : Derivation (presentation X) Γ j)
    (r : ∀ i, Derivation (presentation X) Δ (Γ.claim i))
    (h : ∀ i, (model ρ C σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model ρ C σ) h = d.eval (model ρ C σ) (fun i => (r i).eval (model ρ C σ) h) :=
  Derivation.eval_substitute _ h d r

/-- A matrix certificate survives event selection and a real quantum channel. -/
def selectProcess (s reference channel : Nat) (event : Finset X) (q : ℝ) :
    Derivation (presentation X) (Logic.Context.singleton (.domination (.state s) reference q))
      (.guessBound (.process (.select (.state s) event) channel) q) :=
  .apply (T := presentation X) (.process _ channel q) (fun _ =>
    .apply (T := presentation X) (.select _ event q) (fun _ =>
      .apply (T := presentation X) (.dominated _ reference q) (fun _ => .hypothesis 0)))

end
end Foundation.Quantum.QKD.SubnormalizedLogic
