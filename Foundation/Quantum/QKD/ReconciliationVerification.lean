import Foundation.Quantum.QKD.KeyVerificationLogic
import Foundation.Quantum.QKD.ReconciliationCorrectness
import Foundation.Quantum.QKD.BB84Collision

/-! Actual repetition decoding followed by an independently seeded public
verification tag. Even uncorrectable inputs have a bounded probability of
passing with different keys. Secrecy of the additionally published tag remains
an obligation; this is not an authenticated full-protocol theorem. -/
namespace Foundation.Quantum.QKD.RepetitionReconciliation
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def fullKey {b : Nat} (x : Fin b → Triple) : Finalization.RawKey (b*3) :=
  fun i => some (x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

theorem fullKey_injective (b : Nat) : Function.Injective (fullKey (b := b)) := by
  intro x y h
  funext j i
  have hh := congrFun h (finProdFinEquiv (j,i))
  simp only [fullKey, Equiv.symm_apply_apply] at hh
  exact Option.some.inj hh

def verificationHash {b tag : Nat} (s : Hashing.RawSeed (b*3) tag) (x : Fin b → Triple) :=
  Hashing.rawHash s (fullKey x)

theorem verification_collision {b tag : Nat} (x y : Fin b → Triple) (h : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform (Hashing.RawSeed (b*3) tag))
      verificationHash x y = 1 / Fintype.card (IdealKey.Key tag) :=
  Collision.raw_collision (fullKey x) (fullKey y) (fun hh => h (fullKey_injective b hh))

def verified {b tag : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :=
  KeyVerification.accepted (process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed (b*3) tag)) verificationHash

def verificationAbort {b tag : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :=
  KeyVerification.aborted (process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed (b*3) tag)) verificationHash

theorem verified_correctness {b tag : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    CommonKey.correctnessError (verified (tag := tag) ρ) ≤
      1 / Fintype.card (IdealKey.Key tag) := by
  apply KeyVerificationLogic.sound (fun _ => process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed (b*3) tag)) verificationHash
    (1 / Fintype.card (IdealKey.Key tag)) (by positivity)
    (fun x y h => le_of_eq (verification_collision x y h))
    (KeyVerificationLogic.proof _ 0)
  intro i
  exact Fin.elim0 i

/-- The sharper bound also uses the actual bad-error event of the decoder. -/
theorem verified_correctness_bad_event {b tag : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    CommonKey.correctnessError (verified (tag := tag) ρ) ≤
      (1 / Fintype.card (IdealKey.Key tag) : ℝ) *
        mass (restrict ρ (fun x => ∃ j, 1 < errors (x.1 j) (x.2 j))) := by
  exact (KeyVerification.correctness_le (process ρ) _ verificationHash _
    (fun x y h => le_of_eq (verification_collision x y h))).trans
      (mul_le_mul_of_nonneg_left (process_correctness ρ) (by positivity))

theorem verified_branch_mass {b tag : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    mass (verified (tag := tag) ρ) + mass (verificationAbort (tag := tag) ρ) = mass ρ := by
  rw [verified, verificationAbort, KeyVerification.branch_mass, process_mass]

end
end Foundation.Quantum.QKD.RepetitionReconciliation
