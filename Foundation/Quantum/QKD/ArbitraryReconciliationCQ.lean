import Foundation.Quantum.QKD.ArbitraryReconciliation
import Foundation.Quantum.QKD.VerifiedHashBothKeys
import Foundation.Quantum.QKD.KeyVerificationLogic

/-! Actual arbitrary-length decoding on correlated CQ inputs, retaining the
old public record, the full syndrome/suffix message and all Eve entries. -/
namespace Foundation.Quantum.QKD.ArbitraryReconciliation
noncomputable section
open Subnormalized RepetitionReconciliation
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def process {n : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :=
  relabel ρ (fun x => ((x.1.1,decode x.1.2 (message x.1.1)),(x.2,message x.1.1)))

theorem process_mass {n : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) : mass (process ρ) = mass ρ := mass_relabel _ _

theorem process_alice {n : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :
    CommonKey.aliceView (process ρ) =
      relabel (CommonKey.aliceView ρ) (fun x => (x.1,(x.2,message x.1))) := by
  unfold CommonKey.aliceView process
  rw [relabel_comp, relabel_comp]
  rfl

theorem process_correctness {n : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :
    CommonKey.correctnessError (process ρ) ≤
      mass (restrict ρ (fun x => ∃ j, 1 < errors (block x.1.1 j) (block x.1.2 j))) := by
  rw [VerifiedHash.correctness_mass, process, restrict_relabel, mass_relabel,
    mass_restrict, mass_restrict]
  apply Finset.sum_le_sum
  intro x _
  by_cases hb : ∃ j, 1 < errors (block x.1.1 j) (block x.1.2 j)
  · simp only [hb, ite_true]
    split_ifs
    · exact le_rfl
    · exact (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1
  · have hc : ∀ j, errors (block x.1.1 j) (block x.1.2 j) ≤ 1 := by
      intro j
      by_contra hj
      exact hb ⟨j,by omega⟩
    simp only [decode_correct _ _ hc, ne_eq, not_true_eq_false, hb, ite_false]
    exact le_rfl

def fullKey {n : Nat} (x : Word n) : Finalization.RawKey n := fun i => some (x i)

theorem fullKey_injective (n : Nat) : Function.Injective (fullKey (n := n)) := by
  intro x y h
  funext i
  exact Option.some.inj (congrFun h i)

def verificationHash {n tag : Nat} (s : Hashing.RawSeed n tag) (x : Word n) :=
  Hashing.rawHash s (fullKey x)

theorem verification_collision {n tag : Nat} (x y : Word n) (h : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform (Hashing.RawSeed n tag)) verificationHash x y =
      1 / Fintype.card (IdealKey.Key tag) :=
  Collision.raw_collision _ _ (fun hh => h (fullKey_injective n hh))

def verified {n tag : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :=
  KeyVerification.accepted (process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) verificationHash

def aborted {n tag : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :=
  KeyVerification.aborted (process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) verificationHash

theorem verified_correctness {n tag : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :
    CommonKey.correctnessError (verified (tag := tag) ρ) ≤ 1 / Fintype.card (IdealKey.Key tag) := by
  apply KeyVerificationLogic.sound (fun _ => process ρ)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) verificationHash
    (1 / Fintype.card (IdealKey.Key tag)) (by positivity)
    (fun a b hab => le_of_eq (verification_collision a b hab)) (KeyVerificationLogic.proof _ 0)
  intro i
  exact Fin.elim0 i

theorem verified_bad_event {n tag : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :
    CommonKey.correctnessError (verified (tag := tag) ρ) ≤
      (1 / Fintype.card (IdealKey.Key tag) : ℝ) *
        mass (restrict ρ (fun x => ∃ j, 1 < errors (block x.1.1 j) (block x.1.2 j))) :=
  (KeyVerification.correctness_le (process ρ) _ verificationHash _
    (fun a b hab => le_of_eq (verification_collision a b hab))).trans
    (mul_le_mul_of_nonneg_left (process_correctness ρ) (by positivity))

theorem branch_mass {n tag : Nat} {T : Type} [Fintype T] [DecidableEq T] {e : Space}
    (ρ : State ((Word n × Word n) × T) e) :
    mass (verified (tag := tag) ρ) + mass (aborted (tag := tag) ρ) = mass ρ := by
  rw [verified, aborted, KeyVerification.branch_mass, process_mass]

end
end Foundation.Quantum.QKD.ArbitraryReconciliation
