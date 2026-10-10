import Foundation.Quantum.QKD.PairwisePhaseDomination

/-! The complementary phase support is an explicit Hamming-weight band around
the actual recorded test weight, not an independently assumed support set. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

def weight {n : Nat} (z : (qubits n).Basis) : Nat :=
  (Finset.univ.filter (fun i => readBits z i = 1)).card

def testedWeight {n : Nat} (T : Finset (Fin n)) (r : (qubits n).Basis) : Nat :=
  (T.filter (fun i => readBits r i = 1)).card

theorem flip_selection {n : Nat} (θ : Fin n → BB84Basis) (i : Fin n) :
    PairwiseSampling.flip (selection θ i) = selectBit (BB84SiftingRandomness.opposite (θ i)) := by
  cases h : θ i <;> simp [selection, selectBit, PairwiseSampling.flip, h, BB84SiftingRandomness.opposite]

theorem remaining_split {n : Nat} (c : PairwiseSampling.Configuration n) (r z : (qubits n).Basis) :
    PairwiseSampling.remaining (pairBits (split n (basis c) (r,z))) c.1 = weight z := by
  have hs : selection (basis c) = c.1 := (selectorEquiv n).apply_symm_apply c.1
  have hb := (bits n (basis c) (split n (basis c) (r,z))).2
  rw [split_involution] at hb
  rw [← hs]
  unfold PairwiseSampling.remaining weight
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  rw [flip_selection, ← complementary_bits, ← hb]

theorem tested_split {n : Nat} (c : PairwiseSampling.Configuration n) (r z : (qubits n).Basis) :
    PairwiseSampling.tested (pairBits (split n (basis c) (r,z))) c = testedWeight c.2 r := by
  have hs : selection (basis c) = c.1 := (selectorEquiv n).apply_symm_apply c.1
  have h := PairwiseQuantumSampling.observed_tested (e := .unit) (basis c) c.2
    (split n (basis c) (r,z),(():Space.unit.Basis)) (errorCode r) (error_split (e := .unit) _ _ _ ())
  rw [hs] at h
  simpa only [errorCode, Equiv.symm_apply_apply, PairwiseSampling.tested, testedWeight] using h

/-- Integer-scaled Hamming band for the actual error record. No semantic
phase bound is an input to this equivalence. -/
theorem mem_phaseSet {n : Nat} (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r z : (qubits n).Basis) :
    z ∈ phaseSet k gap c r ↔ Nat.dist (n * testedWeight c.2 r) (k * weight z) ≤ gap := by
  simp only [phaseSet, Finset.mem_filter, Finset.mem_univ, true_and, PairwiseSampling.bad]
  rw [tested_split, remaining_split]
  exact not_lt

theorem phaseSet_band {n : Nat} (k gap : Nat) (c : PairwiseSampling.Configuration n)
    (r : (qubits n).Basis) :
    phaseSet k gap c r = Finset.univ.filter
      (fun z => Nat.dist (n * testedWeight c.2 r) (k * weight z) ≤ gap) := by
  ext z
  rw [mem_phaseSet]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
