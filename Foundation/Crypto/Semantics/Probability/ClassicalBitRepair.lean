import Mathlib

/-!
Algebraic and continuity certificates for repairing a noisy classical bit cipher.

The key distribution is independent of the message. Encryption and decryption
are stochastic two-by-two matrices with independent private randomness. Error
is averaged over the key, with a separate bound for each message. Key labels
are retained, while the repair may remove a branch by giving it weight zero.

This file does not certify a bounded fair-coin implementation, a sphere
classification, or a topological nonextension theorem.
-/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section

variable {Key : Type*} [Fintype Key]

structure Cipher (Key : Type*) [Fintype Key] where
  weight : Key → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  enc0 : Key → ℝ
  enc1 : Key → ℝ
  dec0 : Key → ℝ
  dec1 : Key → ℝ
  enc0_mem : ∀ i, enc0 i ∈ Set.Icc 0 1
  enc1_mem : ∀ i, enc1 i ∈ Set.Icc 0 1
  dec0_mem : ∀ i, dec0 i ∈ Set.Icc 0 1
  dec1_mem : ∀ i, dec1 i ∈ Set.Icc 0 1

def error0 (c : Cipher Key) (i : Key) : ℝ :=
  1 - c.enc0 i * c.dec0 i - (1 - c.enc0 i) * c.dec1 i

def error1 (c : Cipher Key) (i : Key) : ℝ :=
  c.enc1 i * c.dec0 i + (1 - c.enc1 i) * c.dec1 i

def signedContrast (c : Cipher Key) (i : Key) : ℝ :=
  c.weight i * (c.enc0 i - c.enc1 i)

def mass (w : Key → ℝ) : ℝ := ∑ i, |w i|
def bias (w : Key → ℝ) : ℝ := ∑ i, w i
def positiveMass (w : Key → ℝ) : ℝ := ∑ i, max (w i) 0
def negativeMass (w : Key → ℝ) : ℝ := ∑ i, max (-w i) 0

theorem branch_contrast_lower (c : Cipher Key) (i : Key) :
    1 - error0 c i - error1 c i ≤ |c.enc0 i - c.enc1 i| := by
  have hd : |c.dec0 i - c.dec1 i| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(c.dec0_mem i).1, (c.dec0_mem i).2,
      (c.dec1_mem i).1, (c.dec1_mem i).2]
  have hmul : (c.enc0 i - c.enc1 i) * (c.dec0 i - c.dec1 i) ≤
      |c.enc0 i - c.enc1 i| := by
    calc
      _ ≤ |(c.enc0 i - c.enc1 i) * (c.dec0 i - c.dec1 i)| := le_abs_self _
      _ = |c.enc0 i - c.enc1 i| * |c.dec0 i - c.dec1 i| := abs_mul _ _
      _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) hd
  dsimp [error0, error1]
  nlinarith [hmul]

/-- Correctness is averaged over keys; no per-key correctness premise occurs. -/
theorem mass_lower_of_correctness (c : Cipher Key) (δ : ℝ)
    (h0 : ∑ i, c.weight i * error0 c i ≤ δ)
    (h1 : ∑ i, c.weight i * error1 c i ≤ δ) :
    1 - 2 * δ ≤ mass (signedContrast c) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (branch_contrast_lower c i) (c.weight_nonneg i)
  have heq : (∑ i, c.weight i * (1 - error0 c i - error1 c i)) =
      1 - (∑ i, c.weight i * error0 c i) - ∑ i, c.weight i * error1 c i := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, c.weight_sum]
  have habs : (∑ i, c.weight i * |c.enc0 i - c.enc1 i|) =
      mass (signedContrast c) := by
    unfold mass signedContrast
    simp_rw [abs_mul, abs_of_nonneg (c.weight_nonneg _)]
  rw [heq, habs] at h
  linarith

theorem parts_difference (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hn : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

theorem parts_sum (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    ring
  · have hn : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), abs_of_nonpos hn]
    ring

theorem mass_parts (w : Key → ℝ) : positiveMass w + negativeMass w = mass w := by
  rw [positiveMass, negativeMass, mass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => parts_sum (w i)

theorem bias_parts (w : Key → ℝ) : positiveMass w - negativeMass w = bias w := by
  rw [positiveMass, negativeMass, bias, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => parts_difference (w i)

/-- Privacy and ordinary correctness give positive normalization denominators. -/
theorem repair_margin (c : Cipher Key) (ε δ : ℝ)
    (h0 : ∑ i, c.weight i * error0 c i ≤ δ)
    (h1 : ∑ i, c.weight i * error1 c i ≤ δ)
    (hprivacy : |bias (signedContrast c)| ≤ ε)
    (hgood : ε + 2 * δ < 1) :
    0 < positiveMass (signedContrast c) ∧ 0 < negativeMass (signedContrast c) := by
  have hm := mass_lower_of_correctness c δ h0 h1
  have hs := mass_parts (signedContrast c)
  have hb := bias_parts (signedContrast c)
  have hbounds := abs_le.mp hprivacy
  constructor <;> linarith [hbounds.1, hbounds.2]

theorem repair_margin_bound (c : Cipher Key) (ε δ μ : ℝ)
    (h0 : ∑ i, c.weight i * error0 c i ≤ δ)
    (h1 : ∑ i, c.weight i * error1 c i ≤ δ)
    (hprivacy : |bias (signedContrast c)| ≤ ε)
    (hgood : ε + 2 * δ ≤ 1 - μ) :
    μ ≤ 2 * positiveMass (signedContrast c) ∧
      μ ≤ 2 * negativeMass (signedContrast c) := by
  have hm := mass_lower_of_correctness c δ h0 h1
  have hs := mass_parts (signedContrast c)
  have hb := bias_parts (signedContrast c)
  have hbounds := abs_le.mp hprivacy
  constructor <;> linarith [hbounds.1, hbounds.2]

def repair (w : Key → ℝ) (i : Key) : ℝ :=
  max (w i) 0 / (2 * positiveMass w) - max (-w i) 0 / (2 * negativeMass w)

theorem repair_bias (w : Key → ℝ)
    (hp : 0 < positiveMass w) (hn : 0 < negativeMass w) :
    bias (repair w) = 0 := by
  unfold bias repair
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  change positiveMass w / (2 * positiveMass w) - negativeMass w / (2 * negativeMass w) = 0
  field_simp; ring

theorem repair_abs (w : Key → ℝ)
    (hp : 0 < positiveMass w) (hn : 0 < negativeMass w) (i : Key) :
    |repair w i| = max (w i) 0 / (2 * positiveMass w) +
      max (-w i) 0 / (2 * negativeMass w) := by
  have hpp : 0 ≤ 2 * positiveMass w := le_of_lt (mul_pos (by norm_num) hp)
  have hnn : 0 ≤ 2 * negativeMass w := le_of_lt (mul_pos (by norm_num) hn)
  by_cases hx : 0 ≤ w i
  · simp only [repair, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
      zero_div, sub_zero, add_zero]
    exact abs_of_nonneg (div_nonneg hx hpp)
  · have hx' : w i ≤ 0 := le_of_not_ge hx
    simp only [repair, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'),
      zero_div, zero_sub, zero_add, abs_neg]
    exact abs_of_nonneg (div_nonneg (neg_nonneg.mpr hx') hnn)

theorem repair_mass (w : Key → ℝ)
    (hp : 0 < positiveMass w) (hn : 0 < negativeMass w) :
    mass (repair w) = 1 := by
  unfold mass
  simp_rw [repair_abs w hp hn]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  change positiveMass w / (2 * positiveMass w) + negativeMass w / (2 * negativeMass w) = 1
  field_simp; ring

theorem repair_fixed (w : Key → ℝ) (hb : bias w = 0) (hm : mass w = 1) :
    repair w = w := by
  have hs := mass_parts w
  have hd := bias_parts w
  have hp : positiveMass w = 1 / 2 := by linarith
  have hn : negativeMass w = 1 / 2 := by linarith
  funext i
  simp [repair, hp, hn]

/-- A signed vector representing a private, exactly reversible bit cipher. -/
structure PerfectCipher (Key : Type*) [Fintype Key] where
  signed : Key → ℝ
  bias_zero : bias signed = 0
  mass_one : mass signed = 1

noncomputable def repairedCipher (c : Cipher Key) (ε δ : ℝ)
    (h0 : ∑ i, c.weight i * error0 c i ≤ δ)
    (h1 : ∑ i, c.weight i * error1 c i ≤ δ)
    (hprivacy : |bias (signedContrast c)| ≤ ε)
    (hgood : ε + 2 * δ < 1) : PerfectCipher Key :=
  let h := repair_margin c ε δ h0 h1 hprivacy hgood
  ⟨repair (signedContrast c), repair_bias _ h.1 h.2, repair_mass _ h.1 h.2⟩

/-- Continuity includes zero-weight branches, where a sign can change. -/
theorem continuous_repair {X : Type*} [TopologicalSpace X] (w : X → Key → ℝ)
    (hw : Continuous w) (hp : ∀ x, 0 < positiveMass (w x))
    (hn : ∀ x, 0 < negativeMass (w x)) : Continuous (fun x => repair (w x)) := by
  have hc (i : Key) : Continuous (fun x => w x i) := (continuous_apply i).comp hw
  have hpos : Continuous (fun x => positiveMass (w x)) :=
    continuous_finsetSum _ fun i _ => (hc i).max continuous_const
  have hneg : Continuous (fun x => negativeMass (w x)) :=
    continuous_finsetSum _ fun i _ => (hc i).neg.max continuous_const
  apply continuous_pi
  intro i
  exact (((hc i).max continuous_const).div (continuous_const.mul hpos)
    (fun x => ne_of_gt (mul_pos (by norm_num) (hp x)))).sub
    (((hc i).neg.max continuous_const).div (continuous_const.mul hneg)
    (fun x => ne_of_gt (mul_pos (by norm_num) (hn x))))

/-- The signed representation yields actual stochastic encryption and decryption. -/
def PerfectCipher.toCipher (d : PerfectCipher Key) : Cipher Key where
  weight i := |d.signed i|
  weight_nonneg i := abs_nonneg _
  weight_sum := d.mass_one
  enc0 i := if 0 ≤ d.signed i then 1 else 0
  enc1 i := if 0 ≤ d.signed i then 0 else 1
  dec0 i := if 0 ≤ d.signed i then 1 else 0
  dec1 i := if 0 ≤ d.signed i then 0 else 1
  enc0_mem i := by split_ifs <;> norm_num
  enc1_mem i := by split_ifs <;> norm_num
  dec0_mem i := by split_ifs <;> norm_num
  dec1_mem i := by split_ifs <;> norm_num

theorem PerfectCipher.toCipher_correct (d : PerfectCipher Key) (i : Key) :
    error0 d.toCipher i = 0 ∧ error1 d.toCipher i = 0 := by
  simp only [error0, error1, PerfectCipher.toCipher]
  split_ifs <;> norm_num

theorem PerfectCipher.toCipher_contrast (d : PerfectCipher Key) :
    signedContrast d.toCipher = d.signed := by
  funext i
  dsimp [signedContrast, PerfectCipher.toCipher]
  by_cases hx : 0 ≤ d.signed i
  · simp [hx, abs_of_nonneg hx]
  · simp [hx, abs_of_neg (lt_of_not_ge hx)]

theorem PerfectCipher.toCipher_weighted0 (d : PerfectCipher Key) (i : Key) :
    d.toCipher.weight i * d.toCipher.enc0 i = max (d.signed i) 0 := by
  dsimp [PerfectCipher.toCipher]
  by_cases hx : 0 ≤ d.signed i
  · simp [hx, abs_of_nonneg hx]
  · simp [hx, max_eq_right (le_of_not_ge hx)]

theorem PerfectCipher.toCipher_weighted1 (d : PerfectCipher Key) (i : Key) :
    d.toCipher.weight i * d.toCipher.enc1 i = max (-d.signed i) 0 := by
  dsimp [PerfectCipher.toCipher]
  by_cases hx : 0 ≤ d.signed i
  · simp [hx]
  · simp [hx, abs_of_neg (lt_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]

/-- Probability of ciphertext zero is one half, for each plaintext separately. -/
theorem PerfectCipher.toCipher_private (d : PerfectCipher Key) :
    (∑ i, d.toCipher.weight i * d.toCipher.enc0 i) = 1 / 2 ∧
    (∑ i, d.toCipher.weight i * d.toCipher.enc1 i) = 1 / 2 := by
  have hs := mass_parts d.signed
  have hd := bias_parts d.signed
  have hp : positiveMass d.signed = 1 / 2 := by
    linarith [d.mass_one, d.bias_zero]
  have hn : negativeMass d.signed = 1 / 2 := by
    linarith [d.mass_one, d.bias_zero]
  constructor
  · simpa only [PerfectCipher.toCipher_weighted0, positiveMass] using hp
  · simpa only [PerfectCipher.toCipher_weighted1, negativeMass] using hn

/-- The actual weighted stochastic entries are continuous even when signs change.
The other ciphertext entries are obtained by subtracting these from the key
weight. Decoder matrices equal encoder matrices in this construction. -/
theorem continuous_perfect_implementation {X : Type*} [TopologicalSpace X]
    (d : X → PerfectCipher Key) (hd : Continuous (fun x => (d x).signed)) :
    Continuous (fun x => fun i =>
      ((d x).toCipher.weight i * (d x).toCipher.enc0 i,
       (d x).toCipher.weight i * (d x).toCipher.enc1 i)) := by
  simp_rw [PerfectCipher.toCipher_weighted0, PerfectCipher.toCipher_weighted1]
  apply continuous_pi
  intro i
  have hc : Continuous (fun x => (d x).signed i) := (continuous_apply i).comp hd
  exact (hc.max continuous_const).prodMk (hc.neg.max continuous_const)

/-- End-to-end repair at the level of finite stochastic matrices. -/
theorem repairedCipher_sound (c : Cipher Key) (ε δ : ℝ)
    (h0 : ∑ i, c.weight i * error0 c i ≤ δ)
    (h1 : ∑ i, c.weight i * error1 c i ≤ δ)
    (hprivacy : |bias (signedContrast c)| ≤ ε)
    (hgood : ε + 2 * δ < 1) :
    let out := (repairedCipher c ε δ h0 h1 hprivacy hgood).toCipher
    (∀ i, error0 out i = 0 ∧ error1 out i = 0) ∧
      (∑ i, out.weight i * out.enc0 i) = 1 / 2 ∧
      (∑ i, out.weight i * out.enc1 i) = 1 / 2 := by
  exact ⟨PerfectCipher.toCipher_correct _, PerfectCipher.toCipher_private _⟩

/-- Family theorem: only the input weighted contrast must vary continuously.
The error bounds may be chosen separately at every parameter. -/
theorem continuous_repairedCipher {X : Type*} [TopologicalSpace X]
    (c : X → Cipher Key) (ε δ : X → ℝ)
    (h0 : ∀ x, ∑ i, (c x).weight i * error0 (c x) i ≤ δ x)
    (h1 : ∀ x, ∑ i, (c x).weight i * error1 (c x) i ≤ δ x)
    (hprivacy : ∀ x, |bias (signedContrast (c x))| ≤ ε x)
    (hgood : ∀ x, ε x + 2 * δ x < 1)
    (hc : Continuous (fun x => signedContrast (c x))) :
    Continuous (fun x =>
      (repairedCipher (c x) (ε x) (δ x) (h0 x) (h1 x) (hprivacy x) (hgood x)).signed) := by
  exact continuous_repair _ hc
    (fun x => (repair_margin (c x) (ε x) (δ x) (h0 x) (h1 x) (hprivacy x) (hgood x)).1)
    (fun x => (repair_margin (c x) (ε x) (δ x) (h0 x) (h1 x) (hprivacy x) (hgood x)).2)

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
