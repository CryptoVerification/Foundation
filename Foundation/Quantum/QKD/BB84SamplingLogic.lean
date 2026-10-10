import Foundation.Quantum.QKD.BB84Sampling
import Foundation.Quantum.QKD.BB84BlockExamples
import Foundation.Logic.Presentation

/-! An independently reconstructed finite calculus for the verified block
experiment and its classical zero-error test. The sampling axiom schema is a
specific combinatorial theorem, not an arbitrary semantic-truth rule. -/
namespace Foundation.Quantum.QKD.BB84SamplingLogic
noncomputable section
open Foundation.Logic Foundation.Probability
open scoped ENNReal

inductive Claim (n : Nat) where
  | failureBound : ℝ≥0∞ → Claim n
  | acceptedBound : Nat → ℝ≥0∞ → Claim n
  | correctness : Nat → ℝ≥0∞ → Claim n
  | zeroTest : (Fin n → Fin 2) → Finset (Fin n) → Claim n
  | undetected : (Fin n → Fin 2) → Finset (Fin n) → Claim n

inductive Rule (n : Nat) where
  | sample : Rule n
  | accepted : Nat → Rule n
  | correctness : Nat → Rule n
  | zeroTest : (Fin n → Fin 2) → Finset (Fin n) → Rule n
  | weaken (ε δ : ℝ≥0∞) (h : ε ≤ δ) : Rule n

abbrev presentation {n : Nat} (alice bob : Fin n → BB84Basis) (k bad : Nat) : Presentation where
  Judgment := Claim n
  Rule := Rule n
  arity := fun | .sample | .accepted .. | .correctness .. => 0 | .zeroTest .. | .weaken .. => 1
  premise := fun
    | .sample | .accepted .. | .correctness .. => Fin.elim0
    | .zeroTest c T => fun _ => .zeroTest c T
    | .weaken ε _ _ => fun _ => .failureBound ε
  conclusion := fun
    | .sample => .failureBound (Sampling.missedErrorBound (RawProtocol.matched alice bob) k bad)
    | .accepted minKey => .acceptedBound minKey
        (Sampling.missedErrorBound (RawProtocol.matched alice bob) k bad)
    | .correctness minKey => .correctness minKey
        (Sampling.missedErrorBound (RawProtocol.matched alice bob) k 1)
    | .zeroTest c T => .undetected c T
    | .weaken _ δ _ => .failureBound δ

variable {n : Nat} {e : Space} (A : BlockAttack n e)
  (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) (k bad : Nat)
  (hk : k ≤ (RawProtocol.matched alice bob).card)

def meaning : Claim n → Prop
  | .failureBound ε => eventProb (RawProtocol.sampledErrors A alice bob b k hk)
      (Sampling.badUndetected (RawProtocol.matched alice bob) bad) ≤ ε
  | .acceptedBound minKey ε => eventProb (RawProtocol.sampledOutcomes A alice bob b k hk)
      (RawProtocol.badAccepted alice bob b minKey bad) ≤ ε
  | .correctness minKey ε => eventProb (RawProtocol.sampledOutcomes A alice bob b k hk)
      (RawProtocol.keyMismatch alice bob b minKey) ≤ ε
  | .zeroTest c T => RawProtocol.errors b c T = 0
  | .undetected c T => Sampling.undetected (RawProtocol.errorPositions b c) T

def model : Model (presentation alice bob k bad) where
  Carrier := meaning A alice bob b k bad hk
  operation := fun r h => by
    cases r with
    | sample => exact RawProtocol.sampledErrors_bound A alice bob b k bad hk
    | accepted minKey => exact RawProtocol.badAccepted_bound A alice bob b k minKey bad hk
    | correctness minKey => exact RawProtocol.keyMismatch_bound A alice bob b k minKey hk
    | zeroTest c T => exact (RawProtocol.zero_errors_iff b c T).mp (h 0)
    | weaken _ _ hεδ => exact (h 0).trans hεδ

theorem sound {Γ : Context (presentation alice bob k bad)} {j}
    (d : Derivation (presentation alice bob k bad) Γ j)
    (h : ∀ i, (model A alice bob b k bad hk).Carrier (Γ.claim i)) :
    (model A alice bob b k bad hk).Carrier j := d.eval _ h

def sampleProof : Derivation (presentation alice bob k bad) (.empty _)
    (.failureBound (Sampling.missedErrorBound (RawProtocol.matched alice bob) k bad)) :=
  .apply (T := presentation alice bob k bad) .sample (fun i => Fin.elim0 i)

/-- Derivation of the unconditioned bad acceptance bound for the actual raw protocol. -/
def acceptedProof (minKey : Nat) : Derivation (presentation alice bob k bad) (.empty _)
    (.acceptedBound minKey (Sampling.missedErrorBound (RawProtocol.matched alice bob) k bad)) :=
  .apply (T := presentation alice bob k bad) (.accepted minKey) (fun i => Fin.elim0 i)

/-- A concrete derivation of the raw-key correctness estimate. -/
def correctnessProof (minKey : Nat) : Derivation (presentation alice bob k bad) (.empty _)
    (.correctness minKey (Sampling.missedErrorBound (RawProtocol.matched alice bob) k 1)) :=
  .apply (T := presentation alice bob k bad) (.correctness minKey) (fun i => Fin.elim0 i)

def zeroTestProof (c : Fin n → Fin 2) (T : Finset (Fin n)) :
    Derivation (presentation alice bob k bad) (.singleton (.zeroTest c T)) (.undetected c T) :=
  .apply (T := presentation alice bob k bad) (.zeroTest c T)
    (fun _ => .hypothesis (T := presentation alice bob k bad) 0)

theorem interpretation_substitute {Γ Δ : Context (presentation alice bob k bad)} {j}
    (d : Derivation (presentation alice bob k bad) Γ j)
    (r : ∀ i, Derivation (presentation alice bob k bad) Δ (Γ.claim i))
    (h : ∀ i, (model A alice bob b k bad hk).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model A alice bob b k bad hk) h =
      d.eval (model A alice bob b k bad hk) (fun i => (r i).eval _ h) :=
  Derivation.eval_substitute _ h d r

/-- The derived estimate is nontrivial for an actual non-product quantum channel. -/
theorem cnot_sample_interpreted :
    eventProb (RawProtocol.sampledErrors BlockExamples.cnotAttack
      (fun _ => .Z) (fun _ => .Z) (fun _ => 1) 1 (by decide))
      (Sampling.badUndetected (RawProtocol.matched (fun _ : Fin 2 => .Z) (fun _ => .Z)) 1) ≤
      (1 / 2 : ℝ≥0∞) := by
  have h := sound BlockExamples.cnotAttack (fun _ => .Z) (fun _ => .Z) (fun _ => 1)
    1 1 (by decide) (sampleProof (fun _ : Fin 2 => .Z) (fun _ => .Z) 1 1) (fun i => Fin.elim0 i)
  change _ ≤ Sampling.missedErrorBound _ 1 1 at h
  convert h using 1; norm_num [Sampling.missedErrorBound, RawProtocol.matched]


/-- Actual raw-key disagreement is bounded for the concrete joint attack. -/
theorem cnot_correctness_interpreted :
    eventProb (RawProtocol.sampledOutcomes BlockExamples.cnotAttack
      (fun _ => .Z) (fun _ => .Z) (fun _ => 1) 1 (by decide))
      (RawProtocol.keyMismatch (fun _ => .Z) (fun _ => .Z) (fun _ => 1) 1) ≤
      (1 / 2 : ℝ≥0∞) := by
  have h := sound BlockExamples.cnotAttack (fun _ => .Z) (fun _ => .Z) (fun _ => 1)
    1 1 (by decide) (correctnessProof (fun _ : Fin 2 => .Z) (fun _ => .Z) 1 1 1)
      (fun i => Fin.elim0 i)
  change _ ≤ Sampling.missedErrorBound _ 1 1 at h
  convert h using 1; norm_num [Sampling.missedErrorBound, RawProtocol.matched]

end
end Foundation.Quantum.QKD.BB84SamplingLogic
