import Foundation.Quantum.QKD.PairwiseReconciledCoordinates
import Foundation.Quantum.QKD.PublicRegisterSeeded

/-! The actual arbitrary-length syndrome and suffix, the verification tag,
and both full-position seeds in privacy amplification of the same supported
BB84 state. Every public message costs its proved finite alphabet size. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

abbrev Disclosure {m : Nat} (tag : Nat) (c : PairwiseSampling.Configuration m) :=
  ArbitraryReconciliation.Message (BB84SiftedInput.remainderCount c.2) × IdealKey.Key tag

def verifiedDisclosure {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  disclose (verifiedSource M v hv k gap minKey tolerance c s)
    (fun x _ => (ArbitraryReconciliation.quantumMessage x,expandedHash M c.2 s x))

def verifiedKey {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  withPublic (withPublic (verifiedDisclosure M v hv k gap minKey tolerance c s))

def coefficient {m : Nat} (tag k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration m) : ℝ :=
  Fintype.card (Disclosure tag c) * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c)

theorem coefficient_nonneg {m : Nat} (tag k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) : 0 ≤ coefficient tag k gap minKey tolerance c :=
  mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (bound_nonneg _ _ _ _ _))

/-- The suffix and every parity bit are explicitly charged, as is the tag. -/
theorem coefficient_public_bits {m : Nat} (tag k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) :
    coefficient tag k gap minKey tolerance c =
      (2:ℝ)^(ArbitraryReconciliation.publicBits (BB84SiftedInput.remainderCount c.2)) *
        Fintype.card (IdealKey.Key tag) * ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) := by
  unfold coefficient
  rw [Fintype.card_prod, ArbitraryReconciliation.message_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem verified_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    Dominated (verifiedKey M v hv k gap minKey tolerance c s)
      (leakedReference (C := Disclosure tag c)
        (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis) (reference v hv k gap c)))
      (coefficient tag k gap minKey tolerance c) :=
  disclose_dominated _ _ _ _ (verified_test_dominated M v hv k gap minKey tolerance c s)

def privacyError {m : Nat} (tag length k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) : ℝ :=
  (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
    ((1-1/Fintype.card (IdealKey.Key length))*(coefficient tag k gap minKey tolerance c * 1)))

theorem verified_privacy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun r => Collision.hashed (verifiedKey M v hv k gap minKey tolerance c s).block (expandedHash M c.2 r)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (verifiedKey M v hv k gap minKey tolerance c s).block))
      (privacyError tag length k gap minKey tolerance c) := by
  apply PrivacyAmplificationLogic.sound _ (expandedHash M c.2)
    (fun _ => verifiedKey M v hv k gap minKey tolerance c s)
    (fun _ => leakedReference (C := Disclosure tag c)
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis) (reference v hv k gap c)))
    (expanded_collision M c.2)
    (PrivacyAmplificationLogic.proof (Fintype.card (IdealKey.Key length)) 0 0
      (coefficient tag k gap minKey tolerance c) 1 _ (coefficient_nonneg _ _ _ _ _ _) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact verified_dominated M v hv k gap minKey tolerance c s
  · have hi1 : i = 1 := by omega
    subst i
    exact (verifiedKey M v hv k gap minKey tolerance c s).bounded

theorem verifiedDisclosure_diagonal {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    PublicRegisterExpose.Diagonal (verifiedDisclosure M v hv k gap minKey tolerance c s) := by
  unfold verifiedDisclosure disclose verifiedSource verifiedAlice
  exact PublicRegisterExpose.relabel_diagonal _
    (PublicRegisterExpose.relabel_diagonal _ (PublicRegisterExpose.withPublic_diagonal _) _) _

/-- Explicit public syndrome/suffix, tag, test and error record, and PA seed.
The independently chosen verification seed is added in the averaged output. -/
def published {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  PublicRegisterExpose.expose (PublicRegisterExpose.expose (HashLayout.output
    (withPublic (verifiedDisclosure M v hv k gap minKey tolerance c s))
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) (expandedHash M c.2)))

theorem published_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (published (length := length) M v hv k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (published (length := length) M v hv k gap minKey tolerance c s)))
      (privacyError tag length k gap minKey tolerance c) := by
  unfold published
  apply PublicRegisterExpose.secrecy
  · rw [show PublicRegisterExpose.expose (HashLayout.output
        (withPublic (verifiedDisclosure M v hv k gap minKey tolerance c s))
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) (expandedHash M c.2)) =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (verifiedDisclosure M v hv k gap minKey tolerance c s))
        (fun rx => (expandedHash M c.2 rx.1 rx.2.1.1,((rx.2.1.2,rx.1),rx.2.2))) from
      PublicRegisterExpose.expose_seed_relabel _ _ _]
    exact PublicRegisterExpose.relabel_diagonal _
      (PublicRegisterExpose.seed_diagonal _ _ (verifiedDisclosure_diagonal M v hv k gap minKey tolerance c s)) _
  · apply PublicRegisterExpose.secrecy _
      (PublicRegisterExpose.hash_output_diagonal _ (PublicRegisterExpose.withPublic_diagonal _) _ _) _
    apply HashLayout.secrecy
    exact verified_privacy M v hv k gap minKey tolerance c s

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
