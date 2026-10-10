import Foundation.Quantum.QKD.VerifiedHashLaws
import Foundation.Quantum.QKD.KeyVerificationSeeded
import Foundation.Quantum.QKD.BB84Collision

/-! Retain both final private keys. Their Alice view is exactly the existing
checked-and-hashed experiment; correctness is bounded by the actual verifier,
not by replacing Bob's key in the real process. -/
namespace Foundation.Quantum.QKD.VerifiedHash
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Same independent PA seed is used locally on both input keys. -/
def pairHash {K T S Y : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype Y]
    [DecidableEq Y] [DecidableEq T] [DecidableEq S] {e : Space}
    (ρ : State ((K × K) × T) e) (p : PMF S) (hash : S → K → Y) :=
  relabel (seed p ρ) (fun sx => ((hash sx.1 sx.2.1.1,hash sx.1 sx.2.1.2),(sx.2.2,sx.1)))

theorem correctness_mass {K T : Type} [Fintype K] [Fintype T] [DecidableEq K] {e : Space}
    (ρ : State ((K × K) × T) e) :
    CommonKey.correctnessError ρ = mass (restrict ρ (fun x => x.1.1 ≠ x.1.2)) := by
  rw [mass_restrict]
  unfold CommonKey.correctnessError
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x.1.1 = x.1.2 <;> simp [hx]

/-- Local hashing cannot turn equal keys into unequal keys. -/
theorem pairHash_correctness {K T S Y : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype Y]
    [DecidableEq K] [DecidableEq Y] [DecidableEq T] [DecidableEq S] {e : Space}
    (ρ : State ((K × K) × T) e) (p : PMF S) (hash : S → K → Y) :
    CommonKey.correctnessError (pairHash ρ p hash) ≤ CommonKey.correctnessError ρ := by
  rw [correctness_mass, pairHash, restrict_relabel, mass_relabel, mass_restrict]
  calc
    _ ≤ mass (seed p (restrict ρ (fun x => x.1.1 ≠ x.1.2))) := by
      rw [seed_restrict, mass_restrict]
      apply Finset.sum_le_sum
      intro sx _
      change (if hash sx.1 sx.2.1.1 ≠ hash sx.1 sx.2.1.2 then
        ((seed p ρ).block sx).trace.re else 0) ≤
        (if sx.2.1.1 ≠ sx.2.1.2 then ((seed p ρ).block sx).trace.re else 0)
      by_cases hx : sx.2.1.1 = sx.2.1.2
      · simp [hx]
      · simp only [hx, ne_eq, not_false_eq_true, ite_true]
        by_cases hh : hash sx.1 sx.2.1.1 = hash sx.1 sx.2.1.2
        · simpa only [hh, not_true_eq_false, ite_false] using
            (Complex.nonneg_iff.mp ((seed p ρ).positive sx).trace_nonneg).1
        · simp [hh]
    _ = CommonKey.correctnessError ρ := by rw [mass_seed, ← correctness_mass]

def bothFixed {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (restrict ρ (fun o => o.transcript.accepted = true))
      (fun o => Hashing.rawHash s o.aliceKey = Hashing.rawHash s o.bobKey)))
    (fun ro => ((Hashing.rawHash ro.1 ro.2.aliceKey,Hashing.rawHash ro.1 ro.2.bobKey),
      (((ro.2.transcript,s),Hashing.rawHash s ro.2.aliceKey),ro.1)))

def bothAverage {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s => bothFixed (length := length) ρ s)

theorem bothFixed_alice {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) : CommonKey.aliceView (bothFixed (length := length) ρ s) = fixed (length := length) ρ s := by
  unfold CommonKey.aliceView bothFixed fixed
  rw [relabel_comp]
  rfl

theorem bothAverage_alice {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    CommonKey.aliceView (bothAverage (tag := tag) (length := length) ρ) = average (tag := tag) (length := length) ρ := by
  unfold CommonKey.aliceView bothAverage average
  rw [mixture_relabel]
  congr 1
  funext s
  exact bothFixed_alice ρ s

def checkedInput {n : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  relabel (restrict ρ (fun o => o.transcript.accepted = true))
    (fun o => ((o.aliceKey,o.bobKey),o.transcript))

/-- This is the earlier actual fresh-seed verification followed by local PA,
with the same tag and public seeds, at the same original branch weights. -/
theorem bothAverage_verifier {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    bothAverage (tag := tag) (length := length) ρ =
      pairHash (KeyVerification.accepted (checkedInput ρ)
        (Foundation.Probability.uniform (Hashing.RawSeed n tag)) Hashing.rawHash)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash := by
  unfold pairHash
  rw [KeyVerification.accepted_mixture, mixture_seed, mixture_relabel]
  unfold bothAverage
  congr 1
  funext s
  unfold KeyVerification.selected checkedInput
  rw [restrict_relabel, seed_relabel, seed_relabel, relabel_comp, relabel_comp]
  rfl

theorem bothAverage_correctness {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    CommonKey.correctnessError (bothAverage (tag := tag) (length := length) ρ) ≤
      1 / Fintype.card (IdealKey.Key tag) := by
  rw [bothAverage_verifier]
  apply le_trans (pairHash_correctness _ _ _)
  exact KeyVerification.correctness_budget _ _ _ _ (by positivity)
    (fun a b hab => le_of_eq (Collision.raw_collision a b hab))

end
end Foundation.Quantum.QKD.VerifiedHash
