import Foundation.Quantum.QKD.BinaryWeightVolume
import Foundation.Quantum.QKD.PairwisePhaseBand
import Foundation.Quantum.QKD.PairwisePhasePublic

/-! The actual accepted phase band embeds in an explicitly counted Hamming
ball. Its radius uses the real test tolerance and integer sampling threshold.
No phase-support cardinality is supplied as an entropy assumption. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def supportRadius (n k gap tolerance : Nat) : Nat := (n*tolerance+gap)/k

theorem bit_ne_zero (b : Fin 2) : b ≠ 0 ↔ b = 1 := by
  fin_cases b <;> decide

theorem accepted_testedWeight {n : Nat} (c : PairwiseSampling.Configuration n)
    (minKey tolerance : Nat) (r : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    testedWeight c.2 r ≤ tolerance := by
  have h := hr.2
  simp only [errorCode, Equiv.symm_apply_apply] at h
  simpa only [bit_ne_zero, testedWeight] using h

theorem accepted_phase_weight {n : Nat} (k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration n) (r z : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r))
    (hz : z ∈ phaseSet k gap c r) : weight z ≤ supportRadius n k gap tolerance := by
  have hband := (mem_phaseSet k gap c r z).mp hz
  have htest := accepted_testedWeight c minKey tolerance r hr
  have hw : k * weight z ≤ n * testedWeight c.2 r + gap := by
    by_cases h : n * testedWeight c.2 r ≤ k * weight z
    · rw [Nat.dist_eq_sub_of_le h] at hband
      omega
    · omega
  have ht := Nat.mul_le_mul_left n htest
  unfold supportRadius
  apply (Nat.le_div_iff_mul_le hk).mpr
  nlinarith

theorem phase_card_le_volume {n : Nat} (k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration n) (r : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (phaseSet k gap c r).card ≤ BinaryWeightVolume.volume n (supportRadius n k gap tolerance) := by
  have hs : (phaseSet k gap c r).map (bitStringEquiv n).toEmbedding ⊆
      BinaryWeightVolume.ball n (supportRadius n k gap tolerance) := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hx
    simp only [BinaryWeightVolume.ball, Finset.mem_filter, Finset.mem_univ, true_and]
    exact accepted_phase_weight k gap minKey tolerance hk c r z hr hz
  have h := Finset.card_le_card hs
  simpa only [Finset.card_map, BinaryWeightVolume.ball_card] using h

theorem acceptedSupport_le_volume {n : Nat} (k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration n) :
    acceptedSupport k gap minKey tolerance c ≤ BinaryWeightVolume.volume n (supportRadius n k gap tolerance) := by
  unfold acceptedSupport
  apply Finset.sup_le
  intro r hr
  have h := (Finset.mem_filter.mp hr).2
  exact phase_card_le_volume k gap minKey tolerance hk c r h

theorem acceptedSupport_zero_short {n : Nat} (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) (h : ¬ minKey ≤ (Finset.univ \ c.2).card) :
    acceptedSupport k gap minKey tolerance c = 0 := by
  simp [acceptedSupport, BB84DelayedDecision.accepts, h]

def volumeBound (n k gap tolerance : Nat) : ℝ :=
  BinaryWeightVolume.volume n (supportRadius n k gap tolerance) * (1/2:ℝ)^n

theorem bound_le_volume {n : Nat} (k gap minKey tolerance : Nat) (hk : 0 < k)
    (c : PairwiseSampling.Configuration n) :
    bound k gap minKey tolerance c ≤ volumeBound n k gap tolerance := by
  unfold bound volumeBound
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast acceptedSupport_le_volume k gap minKey tolerance hk c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
