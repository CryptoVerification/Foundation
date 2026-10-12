import Foundation.Quantum.QKD.ExponentialSecurity

/-! Nontrivial finite-length BB84 security under authentic classical
communication. The leakage envelope uses the actual sifted length, rather
than charging every branch at the largest possible sifted length. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open PairwiseReconciledVerification
set_option backward.isDefEq.respectTransparency false

/-- Six sifted positions pay four public reconciliation bits, while their
weighted support factor contracts by at least one binary digit. -/
theorem six_bit_decay (m : ℕ) :
    (2 : ℝ) ^ (4 * (m / 6)) * (17 / 32 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (m / 6) := by
  have he : (17 / 32 : ℝ) ^ m = ((17 / 32 : ℝ) ^ 6) ^ (m / 6) *
      (17 / 32 : ℝ) ^ (m % 6) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he, pow_mul]
  have hbase : (2 : ℝ) ^ 4 * (17 / 32 : ℝ) ^ 6 ≤ 1 / 2 := by norm_num
  have hrem : (17 / 32 : ℝ) ^ (m % 6) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ = ((2 : ℝ) ^ 4 * (17 / 32 : ℝ) ^ 6) ^ (m / 6) * (17 / 32 : ℝ) ^ (m % 6) := by
      rw [mul_pow]
      ring
    _ ≤ (1 / 2 : ℝ) ^ (m / 6) * 1 :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hbase _) hrem (by positivity) (by positivity)
    _ = _ := mul_one _

private theorem weighted_factor_identity (a b k m r : ℕ) :
    (2 : ℝ) ^ a * (2 : ℝ) ^ b *
      ((2 : ℝ) ^ k * (((17 / 16 : ℝ) ^ m / (1 / 16 : ℝ) ^ r) * (1 / 2 : ℝ) ^ m)) =
      (2 : ℝ) ^ (a + b + k + 4 * r) * (17 / 32 : ℝ) ^ m := by
  have hinv : ((1 / 16 : ℝ) ^ r)⁻¹ = (2 : ℝ) ^ (4 * r) := by
    rw [← inv_pow, pow_mul]
    norm_num
  have hm : (17 / 16 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = (17 / 32 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  rw [div_eq_mul_inv, hinv]
  rw [show (2 : ℝ) ^ (a + b + k + 4 * r) =
      (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ k * (2 : ℝ) ^ (4 * r) by simp [pow_add]]
  calc
    _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ k * (2 : ℝ) ^ (4 * r)) *
        ((17 / 16 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) := by ring
    _ = _ := by rw [hm]

/-- A coefficient envelope retaining the sifted-length reconciliation cost. -/
theorem weightedCoefficient_dyadic_le {m n : ℕ} (hmn : m ≤ n)
    (tag k gap minKey tolerance : ℕ) (hk : k ≤ m) (hk0 : 0 < k) :
    weightedCoefficient m tag k gap minKey tolerance (1 / 16) ≤
      (2 : ℝ) ^ (tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7) *
        (1 / 2 : ℝ) ^ ((k + minKey) / 6) := by
  by_cases hm : minKey ≤ m - k
  · unfold weightedCoefficient
    rw [if_pos hm]
    simp only [IdealKey.Key, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    norm_num only
    rw [weighted_factor_identity]
    let R := PairwisePhaseCoordinates.supportRadius n k gap tolerance
    let c := tag + k / 3 + 4 * R + 7
    have hR : PairwisePhaseCoordinates.supportRadius m k gap tolerance ≤ R :=
      supportRadius_mono k gap tolerance hk0 hmn
    have hpub : ArbitraryReconciliation.publicBits (m - k) + k ≤ 4 * (m / 6) + k / 3 + 7 := by
      unfold ArbitraryReconciliation.publicBits
      omega
    have he : ArbitraryReconciliation.publicBits (m - k) + tag + k +
        4 * PairwisePhaseCoordinates.supportRadius m k gap tolerance ≤ 4 * (m / 6) + c := by
      dsimp [c]
      omega
    have hshort : (k + minKey) / 6 ≤ m / 6 := Nat.div_le_div_right (by omega)
    calc
      _ ≤ (2 : ℝ) ^ (4 * (m / 6) + c) * (17 / 32 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) he) (by positivity)
      _ = (2 : ℝ) ^ c * ((2 : ℝ) ^ (4 * (m / 6)) * (17 / 32 : ℝ) ^ m) := by
        rw [pow_add]
        ring
      _ ≤ (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ (m / 6) :=
        mul_le_mul_of_nonneg_left (six_bit_decay m) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hshort) (by positivity)
  · unfold weightedCoefficient
    rw [if_neg hm]
    positivity

/-- A simple integer budget ensures uniformly small privacy error on every
admissible sifted branch, without evaluating enormous rational powers. -/
theorem weightedPrivacyError_budget {m n : ℕ} (hmn : m ≤ n)
    (tag length k gap minKey tolerance s : ℕ) (hk : k ≤ m) (hk0 : 0 < k)
    (hbudget : length + tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7 + 2 * s ≤
      (k + minKey) / 6) :
    weightedPrivacyError m tag length k gap minKey tolerance (1 / 16) ≤ (1 / 2 : ℝ) ^ s := by
  apply weightedPrivacyError_le
  · positivity
  · have hc := weightedCoefficient_dyadic_le hmn tag k gap minKey tolerance hk hk0
    have h := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ Fintype.card (IdealKey.Key length) by positivity)
    simp only [IdealKey.Key, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    have hp : (1 / 2 : ℝ) ^ ((k + minKey) / 6) ≤
        (1 / 2 : ℝ) ^ (length + tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7 + 2 * s) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hbudget
    let c := length + tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7
    have hmain : (2 : ℝ) ^ length * ((2 : ℝ) ^ (tag + k / 3 +
        4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7) * (1 / 2 : ℝ) ^ ((k + minKey) / 6)) ≤
        (1 / 2 : ℝ) ^ (2 * s) := by
      calc
        _ = (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ ((k + minKey) / 6) := by
          dsimp [c]
          simp only [pow_add]
          ring
        _ ≤ (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ (c + 2 * s) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by
          rw [pow_add (1 / 2 : ℝ) c (2 * s), ← mul_assoc, ← mul_pow]
          norm_num
    have hs : (1 / 2 : ℝ) ^ (2 * s) ≤ (2 * (1 / 2 : ℝ) ^ s) ^ 2 := by
      rw [mul_comm 2 s, pow_mul]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ s)]
    exact h.trans (hmain.trans hs)

theorem countWeightedError_budget (n tag length k gap minKey tolerance s : ℕ) (hk0 : 0 < k)
    (hbudget : length + tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7 + 2 * s ≤
      (k + minKey) / 6) :
    countWeightedError n tag length k gap minKey tolerance (1 / 16) ≤ (1 / 2 : ℝ) ^ s := by
  unfold countWeightedError
  calc
    _ ≤ ∑ m ∈ Finset.range (n + 1), ((Nat.choose n m : ℝ) / (2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ s := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      split_ifs with hk
      · exact weightedPrivacyError_budget (by simp only [Finset.mem_range] at hm; omega)
          tag length k gap minKey tolerance s hk hk0 hbudget
      · positivity
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have hn : (∑ m ∈ Finset.range (n + 1), (Nat.choose n m : ℝ)) = (2 : ℝ) ^ n := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        simp
      rw [hn, div_self (by positivity), one_mul]

/-- A reusable whole-output security theorem with an integer privacy budget
and an exponential sampling bound; its error contains no finite average. -/
theorem real_secure_exponential_budget {n tag length : ℕ} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance s : ℕ) (hk0 : 0 < k) (hg : 0 < gap)
    (hbudget : length + tag + k / 3 + 4 * PairwisePhaseCoordinates.supportRadius n k gap tolerance + 7 + 2 * s ≤
      (k + minKey) / 6) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2 * Real.sqrt (PairwiseSampling.exponentialGapBound n k gap) + (1 / 2 : ℝ) ^ s)) := by
  have h := real_secure_exponential (tag := tag) (length := length) A k gap minKey tolerance
    hk0 hg (1 / 16) (by norm_num) (by norm_num)
  have hp := countWeightedError_budget n tag length k gap minKey tolerance s hk0 hbudget
  intro E
  exact (h E).trans (by linarith)

end
end Foundation.Quantum.QKD.FullReconciledSecurity

namespace Foundation.Quantum.QKD.UsefulBB84
noncomputable section
open FullReconciledSecurity
set_option backward.isDefEq.respectTransparency false

/-- Number of transmitted signals. -/
def signals : ℕ := 25165824
/-- Positions revealed for parameter estimation after sifting. -/
def tests : ℕ := 3145728
/-- Minimum number of unrevealed sifted positions required to continue. -/
def minKey : ℕ := 8388608
/-- Verification-hash output length (not a message-authentication tag). -/
def verificationBits : ℕ := 64
/-- Final privacy-amplified output length. -/
def outputBits : ℕ := 65536
/-- Integer-scaled sampling deviation used only in the security proof. -/
def gap : ℕ := 618475290624
/-- Overall operational real/ideal error guarantee. -/
def securityError : ℝ := (1 / 2 : ℝ) ^ 60

theorem output_positive : 0 < outputBits := by decide

theorem sifting_cutoff_below_mean : tests + minKey < signals / 2 := by decide

theorem privacy_budget :
    outputBits + verificationBits + tests / 3 +
      4 * PairwisePhaseCoordinates.supportRadius signals tests gap 0 + 7 + 2 * 64 ≤
        (tests + minKey) / 6 := by
  norm_num [outputBits, verificationBits, tests, signals, gap, minKey,
    PairwisePhaseCoordinates.supportRadius]

private theorem exp_neg_three_le : Real.exp (-3) ≤ (1 / 16 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) h16

theorem sampling_error_small :
    2 * Real.sqrt (PairwiseSampling.exponentialGapBound signals tests gap) ≤
      4 * (1 / 2 : ℝ) ^ 64 := by
  have h96 : Real.exp (-96) ≤ (1 / 2 : ℝ) ^ 128 := by
    have h := pow_le_pow_left₀ (Real.exp_nonneg (-3)) exp_neg_three_le 32
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have h192 : Real.exp (-192) ≤ Real.exp (-96) := Real.exp_le_exp.mpr (by norm_num)
  have hbound : PairwiseSampling.exponentialGapBound signals tests gap ≤ 4 * (1 / 2 : ℝ) ^ 128 := by
    unfold PairwiseSampling.exponentialGapBound signals tests gap
    norm_num only
    linarith
  have hs : Real.sqrt (PairwiseSampling.exponentialGapBound signals tests gap) ≤
      2 * (1 / 2 : ℝ) ^ 64 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have he : (2 * (1 / 2 : ℝ) ^ 64) ^ 2 = 4 * (1 / 2 : ℝ) ^ 128 := by norm_num
      rwa [he]
  linarith

/-- A nonzero, concrete final key length and a small total error for every
finite-Kraus block attack, including the actual two-key output, public record,
verification/PA seeds and aborts. Classical communication is authentic as
assumed by `realState`; no message-authentication theorem is used here. -/
theorem secure {e : Space} (A : BlockAttack signals e) :
    IdealKey.Secure (realState (tag := verificationBits) (length := outputBits)
      A tests minKey 0) securityError := by
  have h := real_secure_exponential_budget (tag := verificationBits) (length := outputBits)
    A tests gap minKey 0 64 (by decide) (by decide) privacy_budget
  have hc : (1 : ℝ) / Fintype.card (IdealKey.Key verificationBits) = (1 / 2 : ℝ) ^ 64 := by
    norm_num [IdealKey.Key, verificationBits, Fintype.card_fun, Fintype.card_fin]
  have htotal : (1 / 2 : ℝ) ^ 64 + (4 * (1 / 2 : ℝ) ^ 64 + (1 / 2 : ℝ) ^ 64) ≤ securityError := by
    norm_num [securityError]
  intro E
  have hh := h E
  rw [hc] at hh
  exact hh.trans (by linarith [sampling_error_small])

end
end Foundation.Quantum.QKD.UsefulBB84
