import Foundation.Quantum.QKD.BB84RandomizedCorrectness
import Foundation.Quantum.QKD.BB84BlockExamples
import Foundation.Logic.Presentation

/-! The verified randomized raw-key protocol in the existing meta-logic.
The bridge rule connects an actual physical-state observation to ProbComp;
no semantic-truth or ideal-key introduction rule is provided. -/
namespace Foundation.Quantum.QKD.RandomizedLogic
noncomputable section
open Foundation.Logic Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

inductive Claim where
  | physicalCorrectness : ℝ → Claim
  | classicalCorrectness : ℝ → Claim

inductive Rule where
  | sampling : Rule
  | bridge : ℝ → Rule
  | weaken (ε δ : ℝ) (h : ε ≤ δ) : Rule

abbrev presentation (n k : Nat) : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .sampling => 0 | _ => 1
  premise := fun
    | .sampling => Fin.elim0
    | .bridge ε => fun _ => .physicalCorrectness ε
    | .weaken ε _ _ => fun _ => .classicalCorrectness ε
  conclusion := fun
    | .sampling => .physicalCorrectness (Randomized.correctnessBound n k)
    | .bridge ε => .classicalCorrectness ε
    | .weaken _ δ _ => .classicalCorrectness δ

variable {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey : Nat)

def model : Model (presentation n k) where
  Carrier := fun
    | .physicalCorrectness ε =>
      (recordEvent (.tensor (qubits n) e)
        (fun r => Randomized.disagrees ((Fintype.equivFin (RawProtocol.Output n)).symm r))).probability
        (Randomized.record A k minKey 0) ≤ ε
    | .classicalCorrectness ε =>
      (eventProb (Randomized.outcome A k minKey 0) Randomized.disagrees).toReal ≤ ε
  operation := fun r h => by
    cases r with
    | sampling => exact Randomized.physical_correctness A k minKey
    | bridge ε =>
      have hb := h 0
      change _ ≤ ε at hb
      have he := Randomized.record_event A k minKey 0 Randomized.disagrees
      exact he ▸ hb
    | weaken _ _ hεδ => exact (h 0).trans hεδ

theorem sound {Γ : Context (presentation n k)} {j}
    (d : Derivation (presentation n k) Γ j)
    (h : ∀ i, (model A k minKey).Carrier (Γ.claim i)) : (model A k minKey).Carrier j :=
  d.eval _ h

def correctnessProof (n k : Nat) : Derivation (presentation n k) (.empty _)
    (.classicalCorrectness (Randomized.correctnessBound n k)) :=
  .apply (T := presentation n k) (.bridge _) (fun _ =>
    .apply (T := presentation n k) .sampling (fun i => Fin.elim0 i))

theorem interpretation_substitute {Γ Δ : Context (presentation n k)} {j}
    (d : Derivation (presentation n k) Γ j)
    (r : ∀ i, Derivation (presentation n k) Δ (Γ.claim i))
    (h : ∀ i, (model A k minKey).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model A k minKey) h =
      d.eval (model A k minKey) (fun i => (r i).eval _ h) :=
  Derivation.eval_substitute _ h d r

/-- Uniform input bits and both random basis strings, with the non-product CNOT attack. -/
theorem cnot_randomized_interpreted :
    (eventProb (Randomized.outcome BlockExamples.cnotAttack 1 1 0) Randomized.disagrees).toReal ≤ 1 / 2 := by
  have d : Derivation (presentation 2 1) (.empty _) (.classicalCorrectness (1 / 2)) :=
    .apply (T := presentation 2 1) (.weaken _ _ Randomized.two_signal_bound)
      (fun _ => correctnessProof 2 1)
  exact sound BlockExamples.cnotAttack 1 1 d (fun i => Fin.elim0 i)

end
end Foundation.Quantum.QKD.RandomizedLogic
