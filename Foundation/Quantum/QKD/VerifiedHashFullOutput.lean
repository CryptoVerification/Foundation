import Foundation.Quantum.QKD.VerifiedHashBothKeys
import Foundation.Quantum.QKD.AcceptedAbortLogic
import Foundation.Quantum.QKD.SubnormalizedIntersection

/-! A normalized full check-and-PA experiment. Both seeds are independently
sampled and published on every path, including original and check aborts.
Abort outputs contain no private key; comparison keeps every abort block. -/
namespace Foundation.Quantum.QKD.VerifiedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def abortFixed {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict ρ (fun o => ¬ (o.transcript.accepted = true ∧
      Hashing.rawHash s o.aliceKey = Hashing.rawHash s o.bobKey))))
    (fun ro => (((ro.2.transcript,s),Hashing.rawHash s ro.2.aliceKey),ro.1))

def abortAverage {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s => abortFixed (length := length) ρ s)

theorem fixed_branch_mass {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) :
    mass (bothFixed (length := length) ρ s) + mass (abortFixed (length := length) ρ s) = mass ρ := by
  unfold bothFixed abortFixed
  rw [mass_relabel, mass_relabel, mass_seed, mass_seed, restrict_intersection]
  exact mass_partition _ _

theorem mass_mixture {S X : Type} [Fintype S] [Fintype X] {e : Space}
    (p : PMF S) (ρ : S → State X e) : mass (mixture p ρ) = ∑ s, (p s).toReal * mass (ρ s) := by
  simp only [mass, mixture, Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_branch_mass {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    mass (bothAverage (tag := tag) (length := length) ρ) +
      mass (abortAverage (tag := tag) (length := length) ρ) = mass ρ := by
  unfold bothAverage abortAverage
  rw [mass_mixture, mass_mixture, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, fixed_branch_mass]
  rw [← Finset.sum_mul, Density.probability_weights, one_mul]

/-- Both old aborts and tag-check failures remain at their actual weights.
Publishing the independent PA seed on abort is part of this specified protocol. -/
def fullState {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (h : mass ρ = 1) :=
  AcceptedAbort.state (bothAverage (tag := tag) (length := length) ρ)
    (abortAverage (tag := tag) (length := length) ρ) (by rw [average_branch_mass, h])

/-- The finite compose/finish derivation uses proved collision correctness
and the supplied Alice secrecy theorem. It introduces no semantic truth rule. -/
theorem full_secure {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (h : mass ρ = 1) (ε : ℝ)
    (hs : OperatorApprox (joint (average (tag := tag) (length := length) ρ))
      (joint (CommonKey.uniformize (average (tag := tag) (length := length) ρ))) ε) :
    IdealKey.Secure (fullState (tag := tag) (length := length) ρ h)
      (1 / Fintype.card (IdealKey.Key tag) + ε) := by
  unfold fullState
  apply AcceptedAbortLogic.sound
    (fun _ => bothAverage (tag := tag) (length := length) ρ)
    (fun _ => abortAverage (tag := tag) (length := length) ρ)
    (fun _ => by rw [average_branch_mass, h])
    (AcceptedAbortLogic.proof 0 (1 / Fintype.card (IdealKey.Key tag)) ε)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact bothAverage_correctness ρ
  · have hi1 : i = 1 := by omega
    subst i
    change OperatorApprox _ _ ε
    rw [bothAverage_alice]
    exact hs

end
end Foundation.Quantum.QKD.VerifiedHash
