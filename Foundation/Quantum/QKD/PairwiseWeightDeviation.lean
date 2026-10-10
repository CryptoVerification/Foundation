import Foundation.Quantum.QKD.PairwiseSampling
import Foundation.Quantum.RecordObservation

/-! First component of Bouman--Fehr Appendix B.5: the signed difference
between selected and complementary bits. Uniform coordinate flips cancel
cross moments, without assuming any independence in the error pattern. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

theorem flip_flip (b : Fin 2) : flip (flip b) = b := by
  fin_cases b <;> decide

def flipEquiv : Fin 2 ≃ Fin 2 where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

def coordinateFlip {n : Nat} (i : Fin n) : (Fin n → Fin 2) ≃ (Fin n → Fin 2) :=
  Equiv.piCongrRight (fun j => if j = i then flipEquiv else Equiv.refl _)

theorem coordinateFlip_self {n : Nat} (i : Fin n) (s : Fin n → Fin 2) :
    coordinateFlip i s i = flip (s i) := by
  simp [coordinateFlip, flipEquiv]

theorem coordinateFlip_other {n : Nat} (i j : Fin n) (h : j ≠ i) (s : Fin n → Fin 2) :
    coordinateFlip i s j = s j := by
  simp [coordinateFlip, h]

def signedBit {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) (i : Fin n) : ℝ :=
  (q (i,s i)).val - (q (i,flip (s i))).val

def weightDifference {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) : ℝ :=
  ∑ i, signedBit q s i

theorem signedBit_flip {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) (i : Fin n) :
    signedBit q (coordinateFlip i s) i = -signedBit q s i := by
  simp only [signedBit, coordinateFlip_self, flip_flip]
  ring

theorem signedBit_other {n : Nat} (q : Pattern n) (s : Fin n → Fin 2)
    (i j : Fin n) (h : j ≠ i) :
    signedBit q (coordinateFlip i s) j = signedBit q s j := by
  simp only [signedBit, coordinateFlip_other i j h]

theorem signedBit_sq_le_one {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) (i : Fin n) :
    signedBit q s i ^ 2 ≤ 1 := by
  have ha : (q (i,s i)).val ≤ 1 := by omega
  have hb : (q (i,flip (s i))).val ≤ 1 := by omega
  have ha' : (q (i,s i)).val = 0 ∨ (q (i,s i)).val = 1 := by omega
  have hb' : (q (i,flip (s i))).val = 0 ∨ (q (i,flip (s i))).val = 1 := by omega
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> norm_num [signedBit, ha', hb']

theorem signedBit_sum_zero {n : Nat} (q : Pattern n) (i : Fin n) :
    ∑ s : Fin n → Fin 2, signedBit q s i = 0 := by
  have h := (coordinateFlip i).sum_comp (fun s => signedBit q s i)
  simp only [signedBit_flip, Finset.sum_neg_distrib] at h
  linarith

theorem cross_sum_zero {n : Nat} (q : Pattern n) (i j : Fin n) (hij : j ≠ i) :
    ∑ s : Fin n → Fin 2, signedBit q s i * signedBit q s j = 0 := by
  have h := (coordinateFlip i).sum_comp (fun s => signedBit q s i * signedBit q s j)
  simp only [signedBit_flip, signedBit_other q _ i j hij, neg_mul, Finset.sum_neg_distrib] at h
  linarith

theorem weightDifference_mean_zero {n : Nat} (q : Pattern n) :
    ∑ s : Fin n → Fin 2, weightDifference q s = 0 := by
  unfold weightDifference
  rw [Finset.sum_comm]
  simp only [signedBit_sum_zero, Finset.sum_const_zero]

/-- The unnormalized second moment is at most cardinality times n. -/
theorem weightDifference_second_moment {n : Nat} (q : Pattern n) :
    ∑ s : Fin n → Fin 2, weightDifference q s ^ 2 ≤
      (Fintype.card (Fin n → Fin 2) : ℝ) * n := by
  have hexpand : (∑ s : Fin n → Fin 2, weightDifference q s ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ s : Fin n → Fin 2, signedBit q s i * signedBit q s j := by
    simp only [weightDifference, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hexpand]
  have hdiag (i : Fin n) :
      (∑ j : Fin n, ∑ s : Fin n → Fin 2, signedBit q s i * signedBit q s j) =
        ∑ s : Fin n → Fin 2, signedBit q s i ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp only [pow_two]
    · intro j _ hji
      exact cross_sum_zero q i j hji
    · simp
  simp_rw [hdiag]
  calc
    _ ≤ ∑ _i : Fin n, ∑ _s : Fin n → Fin 2, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun s _ => signedBit_sq_le_one q s i)
    _ = _ := by simp; ring

/-- The selected side is the whole n-bit side, before the k tests are chosen. -/
def selectedWeight {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) : Nat :=
  (Finset.univ.filter (fun i => q (i,s i) = 1)).card

theorem bit_value (b : Fin 2) : (b.val : ℝ) = if b = 1 then 1 else 0 := by
  fin_cases b <;> norm_num

theorem selectedWeight_sum {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) :
    (selectedWeight q s : ℝ) = ∑ i, ((q (i,s i)).val : ℝ) := by
  simp only [bit_value, Finset.sum_boole, selectedWeight]

theorem remaining_sum {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) :
    (remaining q s : ℝ) = ∑ i, ((q (i,flip (s i))).val : ℝ) := by
  simp only [bit_value, Finset.sum_boole, remaining]

theorem weightDifference_counts {n : Nat} (q : Pattern n) (s : Fin n → Fin 2) :
    weightDifference q s = (selectedWeight q s : ℝ) - remaining q s := by
  simp only [weightDifference, signedBit, Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a-b) (selectedWeight_sum q s).symm (remaining_sum q s).symm

/-- Normalized variance bound for the actual independent uniform two-choice seed. -/
theorem weightDifference_uniform_second_moment {n : Nat} (q : Pattern n) :
    ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * weightDifference q s ^ 2 ≤ n := by
  have hc : (0 : ℝ) < Fintype.card (Fin n → Fin 2) := by positivity
  have hw (s : Fin n → Fin 2) : (uniform (Fin n → Fin 2) s).toReal =
      (1 / (Fintype.card (Fin n → Fin 2) : ℝ)) := by
    simp [uniform, PMF.uniformOfFintype_apply]
  simp_rw [hw]
  rw [← Finset.mul_sum]
  have h := weightDifference_second_moment q
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm] using h

/-- A polynomial tail bound, derived here rather than postulated. This is
only the selected/complementary component of the full sampling error. -/
theorem weightDifference_tail {n : Nat} (q : Pattern n) (t : ℝ) (ht : 0 < t) :
    (eventProb (uniform (Fin n → Fin 2)) (fun s => t < |weightDifference q s|)).toReal ≤
      n / t^2 := by
  classical
  have hmoment := weightDifference_uniform_second_moment q
  have htail : t^2 * (eventProb (uniform (Fin n → Fin 2))
      (fun s => t < |weightDifference q s|)).toReal ≤
      ∑ s : Fin n → Fin 2, (uniform (Fin n → Fin 2) s).toReal * weightDifference q s ^ 2 := by
    rw [eventProb_toReal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : t < |weightDifference q s|
    · simp only [hs, ite_true]
      have hsq : t^2 ≤ weightDifference q s ^ 2 := by
        nlinarith [sq_abs (weightDifference q s), abs_nonneg (weightDifference q s)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (show 0 ≤ (uniform (Fin n → Fin 2) s).toReal from ENNReal.toReal_nonneg)
    · simp only [hs, ite_false, mul_zero]
      positivity
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith

end
end Foundation.Quantum.QKD.PairwiseSampling
