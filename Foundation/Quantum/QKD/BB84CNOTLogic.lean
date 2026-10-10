import Foundation.Quantum.QKD.BB84DecisionRaw
import Foundation.Quantum.MixtureLaws
import Foundation.Logic.Presentation

/-! Finite inference for the proved CNOT experiment transformation, actual
measurement records, randomized bases and physical subsequent processing.
These rules are independently designed; no arbitrary semantic truth rule is
included and the existing metaproof kernel is unchanged. -/
namespace Foundation.Quantum.QKD.BB84CNOTLogic
noncomputable section
open Foundation.Logic BB84ErrorTransform
set_option backward.isDefEq.respectTransparency false

inductive Claim (n : Nat) where
  | coherent (θ : Fin n → BB84Basis)
  | recorded (θ : Fin n → BB84Basis)
  | delayed (θ : Fin n → BB84Basis)
  | decision (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | raw (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | decidedRaw (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | mixed (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m))
  | processed (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat)

inductive Rule (n : Nat) where
  | coherent (θ : Fin n → BB84Basis)
  | record (θ : Fin n → BB84Basis)
  | delay (θ : Fin n → BB84Basis)
  | decide (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | rawOutput (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | decisionRaw (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
  | mix (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m))
  | post (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat)

abbrev presentation (n : Nat) : Presentation where
  Judgment := Claim n
  Rule := Rule n
  arity := fun | .coherent _ => 0 | .mix m .. => m | _ => 1
  premise := fun
    | .coherent _ => Fin.elim0
    | .record θ | .delay θ | .decide θ .. | .rawOutput θ .. | .decisionRaw θ .. => fun _ => .coherent θ
    | .mix _ θ _ => fun i => .recorded (θ i)
    | .post m θ p _ => fun _ => .mixed m θ p
  conclusion := fun
    | .coherent θ => .coherent θ
    | .record θ => .recorded θ
    | .delay θ => .delayed θ
    | .decide θ T l t => .decision θ T l t
    | .rawOutput θ T l t => .raw θ T l t
    | .decisionRaw θ T l t => .decidedRaw θ T l t
    | .mix m θ p => .mixed m θ p
    | .post m θ p c => .processed m θ p c

abbrev recordSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (Fintype.card (Space.tensor (qubits n) (qubits n)).Basis)) e

variable {n : Nat} {e : Space}

def model (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e))
    (C : Nat → Channel (recordSpace n e) (recordSpace n e)) : Model (presentation n) where
  Carrier := fun
    | .coherent θ => ((original n θ).amplify e).toKraus.apply ρ.matrix =
        ((modified n θ).amplify e).toKraus.apply ρ.matrix
    | .recorded θ => (recordedOriginal θ ρ).matrix = (recordedModified θ ρ).matrix
    | .delayed θ =>
        (BB84DelayedMeasurements.delayed θ e).toKraus.apply
          (((original n θ).amplify e).toKraus.apply ρ.matrix) =
        (BB84DelayedMeasurements.joint θ e).toKraus.apply
          (((modified n θ).amplify e).toKraus.apply ρ.matrix)
    | .decision θ T l t =>
        (BB84DelayedDecision.before θ e T l t).record.toKraus.apply
          (((original n θ).amplify e).toKraus.apply ρ.matrix) =
        (BB84DelayedDecision.after θ e T l t).record.toKraus.apply
          (((modified n θ).amplify e).toKraus.apply ρ.matrix)
    | .raw θ T l t =>
        (BB84DeferredRaw.deferred θ e T l t).toKraus.apply ρ.matrix =
          (BB84DeferredRaw.reference θ e T l t).toKraus.apply ρ.matrix
    | .decidedRaw θ T l t =>
        (BB84DecisionRaw.decided θ e T l t).toKraus.apply ρ.matrix =
          (BB84DeferredRaw.reference θ e T l t).toKraus.apply ρ.matrix
    | .mixed _ θ p => (Density.mixture p (fun i => recordedOriginal (θ i) ρ)).matrix =
        (Density.mixture p (fun i => recordedModified (θ i) ρ)).matrix
    | .processed _ θ p c =>
        ((C c).run (Density.mixture p (fun i => recordedOriginal (θ i) ρ))).matrix =
          ((C c).run (Density.mixture p (fun i => recordedModified (θ i) ρ))).matrix
  operation := fun r hs => by
    cases r with
    | coherent θ => exact amplified n θ e ρ.matrix
    | record θ => exact recorded_of_amplified θ ρ (hs 0)
    | delay θ => exact BB84DelayedMeasurements.of_coherent θ ρ.matrix (hs 0)
    | decide θ T l t => exact BB84DelayedDecision.of_coherent θ T l t ρ.matrix (hs 0)
    | rawOutput θ T l t => exact BB84DeferredRaw.output_of_coherent θ T l t ρ.matrix (hs 0)
    | decisionRaw θ T l t => exact BB84DecisionRaw.output_of_coherent θ T l t ρ.matrix (hs 0)
    | mix m θ p => exact Density.mixture_congr_matrix p _ _ hs
    | post m θ p c => exact congrArg (C c).toKraus.apply (hs 0)

theorem sound (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e))
    (C : Nat → Channel (recordSpace n e) (recordSpace n e))
    {Γ : Context (presentation n)} {j} (d : Derivation (presentation n) Γ j)
    (hs : ∀ i, (model ρ C).Carrier (Γ.claim i)) : (model ρ C).Carrier j := d.eval _ hs

theorem interpretation_substitute (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e))
    (C : Nat → Channel (recordSpace n e) (recordSpace n e))
    {Γ Δ : Context (presentation n)} {j} (d : Derivation (presentation n) Γ j)
    (f : ∀ i, Derivation (presentation n) Δ (Γ.claim i))
    (hs : ∀ i, (model ρ C).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model ρ C) hs =
      d.eval (model ρ C) (fun i => (f i).eval (model ρ C) hs) :=
  Derivation.eval_substitute _ hs d f

def proof (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat) :
    Derivation (presentation n) (.empty _) (.processed m θ p c) := by
  apply Derivation.apply (T := presentation n) (.post m θ p c)
  intro _
  apply Derivation.apply (T := presentation n) (.mix m θ p)
  intro i
  apply Derivation.apply (T := presentation n) (.record (θ i))
  intro _
  apply Derivation.apply (T := presentation n) (.coherent (θ i))
  intro j
  exact Fin.elim0 j

/-- Actual closed derivation of the error-first measurement experiment. -/
def delayedProof (θ : Fin n → BB84Basis) :
    Derivation (presentation n) (.empty _) (.delayed θ) := by
  apply Derivation.apply (T := presentation n) (.delay θ)
  intro _
  apply Derivation.apply (T := presentation n) (.coherent θ)
  intro i
  exact Fin.elim0 i

/-- Closed derivation retaining both public accept and abort records. -/
def decisionProof (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Derivation (presentation n) (.empty _) (.decision θ T minKey tolerance) := by
  apply Derivation.apply (T := presentation n) (.decide θ T minKey tolerance)
  intro _
  apply Derivation.apply (T := presentation n) (.coherent θ)
  intro i
  exact Fin.elim0 i

/-- Closed derivation of the existing raw output after signal discard. -/
def rawProof (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Derivation (presentation n) (.empty _) (.raw θ T minKey tolerance) := by
  apply Derivation.apply (T := presentation n) (.rawOutput θ T minKey tolerance)
  intro _
  apply Derivation.apply (T := presentation n) (.coherent θ)
  intro i
  exact Fin.elim0 i

/-- Closed derivation of early public decision followed by the existing raw output. -/
def decidedRawProof (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Derivation (presentation n) (.empty _) (.decidedRaw θ T minKey tolerance) := by
  apply Derivation.apply (T := presentation n) (.decisionRaw θ T minKey tolerance)
  intro _
  apply Derivation.apply (T := presentation n) (.coherent θ)
  intro i
  exact Fin.elim0 i

end
end Foundation.Quantum.QKD.BB84CNOTLogic
