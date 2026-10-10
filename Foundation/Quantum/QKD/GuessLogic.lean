import Foundation.Quantum.QKD.GuessLeakage
import Foundation.Logic.Presentation

/-! Finite derivations from concrete positive-operator domination to optimal
quantum guessing bounds and finite public leakage. Domination is a hypothesis,
not a rule admitting arbitrary semantic truths; concrete examples discharge
it by matrix proofs. The calculus is our independent reconstruction. -/
namespace Foundation.Quantum.QKD.GuessLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | domination (state reference : Nat) (q : ℝ)
  | priorBound (state : Nat) (q : ℝ)
  | priorOptimal (state : Nat) (q : ℝ)
  | leakedOptimal (state : Nat) (q : ℝ)

inductive Rule where
  | dominated (state reference : Nat) (q : ℝ)
  | optimal (state : Nat) (q : ℝ)
  | leak (state : Nat) (q : ℝ)
  | universal (state : Nat)
  | weakenPrior (state : Nat) (q r : ℝ) (h : q ≤ r)
  | weakenLeak (state : Nat) (q r : ℝ) (h : q ≤ r)

abbrev presentation (leakCard : Nat) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .universal .. => 0 | _ => 1
  premise := fun
    | .universal .. => Fin.elim0
    | .dominated s r q => fun _ => .domination s r q
    | .optimal s q => fun _ => .priorBound s q
    | .leak s q | .weakenPrior s q _ _ => fun _ => .priorOptimal s q
    | .weakenLeak s q _ _ => fun _ => .leakedOptimal s q
  conclusion := fun
    | .dominated s _ q => .priorBound s q
    | .universal s => .priorBound s 1
    | .optimal s q => .priorOptimal s q
    | .leak s q => .leakedOptimal s (leakCard*q)
    | .weakenPrior s _ r _ => .priorOptimal s r
    | .weakenLeak s _ r _ => .leakedOptimal s r

variable {X L : Type} [Fintype X] [Fintype L] {e : Space}

def model (ρ : Nat → Guessing.CQ (X × L) e) (σ : Nat → Density e) : Model (presentation (Fintype.card L)) where
  Carrier := fun
    | .domination s r q => Guessing.Dominated (Guessing.hideLeak (ρ s)) (σ r) q
    | .priorBound s q => Guessing.GuessBound (Guessing.hideLeak (ρ s)) q
    | .priorOptimal s q => Guessing.guessingProbability (Guessing.hideLeak (ρ s)) ≤ q
    | .leakedOptimal s q => Guessing.leakedGuessingProbability (ρ s) ≤ q
  operation := fun r h => by
    cases r with
    | dominated s r q => exact Guessing.dominated_guessBound _ _ _ (h 0)
    | optimal s q => exact (Guessing.guessingProbability_le_iff _ _).mpr (h 0)
    | leak s q => exact (Guessing.leakage_chain _).trans (mul_le_mul_of_nonneg_left (h 0) (Nat.cast_nonneg _))
    | universal s => exact fun M => Guessing.score_le_one _ M
    | weakenPrior s q r hqr => exact (h 0).trans hqr
    | weakenLeak s q r hqr => exact (h 0).trans hqr

theorem sound (ρ : Nat → Guessing.CQ (X × L) e) (σ : Nat → Density e)
    {Γ : Logic.Context (presentation (Fintype.card L))} {j}
    (d : Derivation (presentation (Fintype.card L)) Γ j)
    (h : ∀ i, (model ρ σ).Carrier (Γ.claim i)) : (model ρ σ).Carrier j := d.eval _ h

theorem interpretation_substitute (ρ : Nat → Guessing.CQ (X × L) e) (σ : Nat → Density e)
    {Γ Δ : Logic.Context (presentation (Fintype.card L))} {j}
    (d : Derivation (presentation (Fintype.card L)) Γ j)
    (r : ∀ i, Derivation (presentation (Fintype.card L)) Δ (Γ.claim i))
    (h : ∀ i, (model ρ σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model ρ σ) h = d.eval (model ρ σ) (fun i => (r i).eval (model ρ σ) h) :=
  Derivation.eval_substitute _ h d r

/-- A genuine composite derivation, binding a positive-matrix certificate. -/
def leakProof (leakCard state reference : Nat) (q : ℝ) :
    Derivation (presentation leakCard) (Logic.Context.singleton (.domination state reference q))
      (.leakedOptimal state (leakCard*q)) :=
  .apply (T := presentation leakCard) (.leak state q) (fun _ =>
    .apply (T := presentation leakCard) (.optimal state q) (fun _ =>
      .apply (T := presentation leakCard) (.dominated state reference q) (fun _ => .hypothesis 0)))

end
end Foundation.Quantum.QKD.GuessLogic
