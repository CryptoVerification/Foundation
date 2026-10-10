import Foundation.Quantum.QKD.RepetitionReconciliation
import Foundation.Quantum.QKD.PairwiseRawHashPrivacy

/-! A specified block repetition syndrome of the actual remaining key is
public before hashing. Its cost is derived, not a secrecy premise. This is
still the support approximant, not the final error-corrected real protocol. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false

def repetitionMessage {n : Nat} (c : PairwiseSampling.Configuration n) (b : Nat)
    (h : BB84SiftedInput.remainderCount c.2 = b*3)
    (x : (qubits (BB84SiftedInput.remainderCount c.2)).Basis) : Fin (b*2) → Fin 2 :=
  RepetitionReconciliation.quantumMessage (h ▸ x)

def reconciledAlice {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (b : Nat)
    (h : BB84SiftedInput.remainderCount c.2 = b*3) :=
  Subnormalized.withPublic (Subnormalized.withPublic (Subnormalized.disclose
    (Subnormalized.relabel (acceptedAlice v hv k gap minKey tolerance c) (testEquiv c.2))
    (fun x _ => repetitionMessage c b h x)))

theorem repetition_dominated {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (b : Nat)
    (h : BB84SiftedInput.remainderCount c.2 = b*3) :
    Subnormalized.Dominated (reconciledAlice v hv k gap minKey tolerance c b h)
      (Subnormalized.leakedReference (C := Fin (b*2) → Fin 2)
        (Subnormalized.leakedReference
          (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
          (reference v hv k gap c)))
      ((2:ℝ)^(b*2) * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) :=
  syndrome_dominated v hv k gap minKey tolerance (b*2) c (repetitionMessage c b h)

/-- Interpretation of the existing finite PA derivation, with the actual
specified message charged at two public bits per triple. -/
theorem repetition_privacy {n : Nat} {e : Space} {Y S : Type}
    [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (b : Nat)
    (h : BB84SiftedInput.remainderCount c.2 = b*3)
    (p : PMF S) (hash : S → (qubits (BB84SiftedInput.remainderCount c.2)).Basis → Y)
    (hc : ∀ x x', x ≠ x' → Collision.collision p hash x x' ≤ 1 / Fintype.card Y) :
    (PrivacyAmplificationLogic.model p hash
      (fun _ => reconciledAlice v hv k gap minKey tolerance c b h)
      (fun _ => Subnormalized.leakedReference (C := Fin (b*2) → Fin 2)
        (Subnormalized.leakedReference
          (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
          (reference v hv k gap c))) hc).Carrier
      (.distance 0 ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*
        ((((2:ℝ)^(b*2) * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))))) := by
  apply PrivacyAmplificationLogic.sound p hash _ _ hc
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0
      ((2:ℝ)^(b*2) * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) 1 _
      (mul_nonneg (by positivity)
        (mul_nonneg (by positivity) (bound_nonneg _ _ _ _ _))) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact repetition_dominated v hv k gap minKey tolerance c b h
  · have hi1 : i = 1 := by omega
    subst i
    exact (reconciledAlice v hv k gap minKey tolerance c b h).bounded

/-- The actual optional-position binary-matrix hash; its collision estimate
is proved separately, rather than supplied as a new hypothesis here. -/
theorem repetition_raw_privacy {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (b : Nat)
    (h : BB84SiftedInput.remainderCount c.2 = b*3) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun s => Collision.hashed
          (reconciledAlice v hv k gap minKey tolerance c b h).block (remainingHash c.2 s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (reconciledAlice v hv k gap minKey tolerance c b h).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          (((2:ℝ)^(b*2)*((2:ℝ)^c.2.card*bound k gap minKey tolerance c))*1)))) :=
  repetition_privacy v hv k gap minKey tolerance c b h _
    (remainingHash c.2) (remaining_collision c.2)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
