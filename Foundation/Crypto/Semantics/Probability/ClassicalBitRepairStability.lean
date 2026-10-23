import Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

/-! Quantitative stability of the classical bit-cipher repair. No topological
boundary certificate or bounded-machine realization is assumed proved here. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Key : Type*} [Fintype Key]

def l1Distance (w z : Key → ℝ) : ℝ := ∑ i, |w i - z i|

theorem parts_distance (x y : ℝ) :
    |max x 0 - max y 0| + |max (-x) 0 - max (-y) 0| = |x - y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [max_eq_left hx, max_eq_left hy, max_eq_right (neg_nonpos.mpr hx),
      max_eq_right (neg_nonpos.mpr hy)]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hxy : 0 ≤ x - y := by linarith
    simp [max_eq_left hx, max_eq_right hy', max_eq_right (neg_nonpos.mpr hx),
      max_eq_left (neg_nonneg.mpr hy'), abs_of_nonneg hx, abs_of_nonpos hy',
      abs_of_nonneg hxy]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hxy : x - y ≤ 0 := by linarith
    simp [max_eq_right hx', max_eq_left hy, max_eq_left (neg_nonneg.mpr hx'),
      max_eq_right (neg_nonpos.mpr hy), abs_of_nonpos hx', abs_of_nonneg hy,
      abs_of_nonpos hxy]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hy' : y ≤ 0 := le_of_not_ge hy
    simp only [max_eq_right hx', max_eq_right hy', max_eq_left (neg_nonneg.mpr hx'),
      max_eq_left (neg_nonneg.mpr hy'), sub_self, abs_zero, zero_add]
    rw [show -x - -y = -(x - y) by ring, abs_neg]

/-- Normalize two nonnegative vectors, keeping a denominator on the left. -/
theorem normalized_distance_mul (u v : Key → ℝ) (P Q : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : 0 < P) (hq : 0 < Q)
    (hsu : ∑ i, u i = P) (hsv : ∑ i, v i = Q) :
    P * (∑ i, |u i / P - v i / Q|) ≤ 2 * l1Distance u v := by
  have hpoint (i : Key) : P * |u i / P - v i / Q| ≤
      |u i - v i| + (v i / Q) * |Q - P| := by
    have heq : P * (u i / P - v i / Q) =
        (u i - v i) + (v i / Q) * (Q - P) := by
      field_simp; ring
    calc
      _ = |P * (u i / P - v i / Q)| := by rw [abs_mul, abs_of_pos hp]
      _ ≤ |u i - v i| + |(v i / Q) * (Q - P)| := by rw [heq]; exact abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (div_nonneg (hv i) (le_of_lt hq))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  have hnorm : (∑ i, v i / Q) = 1 := by rw [← Finset.sum_div, hsv, div_self (ne_of_gt hq)]
  have hmass : |Q - P| ≤ l1Distance u v := by
    rw [abs_sub_comm, ← hsu, ← hsv, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul] at hsum
  dsimp [l1Distance] at hmass ⊢
  linarith

theorem normalized_distance_margin (u v : Key → ℝ) (P Q μ : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : 0 < P) (hq : 0 < Q)
    (hsu : ∑ i, u i = P) (hsv : ∑ i, v i = Q) (hm : μ ≤ 2 * P) :
    μ * (∑ i, |u i / P - v i / Q|) ≤ 4 * l1Distance u v := by
  have h := normalized_distance_mul u v P Q hv hp hq hsu hsv
  have hn : 0 ≤ ∑ i, |u i / P - v i / Q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hm hn]

theorem repair_point_distance (w z : Key → ℝ)
    (hpw : 0 < positiveMass w) (hnw : 0 < negativeMass w)
    (hpz : 0 < positiveMass z) (hnz : 0 < negativeMass z) (i : Key) :
    2 * |repair w i - repair z i| ≤
      |max (w i) 0 / positiveMass w - max (z i) 0 / positiveMass z| +
      |max (-w i) 0 / negativeMass w - max (-z i) 0 / negativeMass z| := by
  have heq : 2 * (repair w i - repair z i) =
      (max (w i) 0 / positiveMass w - max (z i) 0 / positiveMass z) -
      (max (-w i) 0 / negativeMass w - max (-z i) 0 / negativeMass z) := by
    unfold repair
    field_simp; ring
  calc
    _ = |2 * (repair w i - repair z i)| := by rw [abs_mul]; norm_num
    _ ≤ _ := by
      rw [heq, sub_eq_add_neg]
      simpa only [abs_neg] using abs_add_le
        (max (w i) 0 / positiveMass w - max (z i) 0 / positiveMass z)
        (-(max (-w i) 0 / negativeMass w - max (-z i) 0 / negativeMass z))

/-- Signed-vector form of the repair estimate; both sign masses stay away from zero. -/
theorem repair_distance_mul (w z : Key → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hpw : μ ≤ 2 * positiveMass w) (hnw : μ ≤ 2 * negativeMass w)
    (hpz : μ ≤ 2 * positiveMass z) (hnz : μ ≤ 2 * negativeMass z) :
    μ * l1Distance (repair w) (repair z) ≤ 2 * l1Distance w z := by
  have pw : 0 < positiveMass w := by linarith
  have nw : 0 < negativeMass w := by linarith
  have pz : 0 < positiveMass z := by linarith
  have nz : 0 < negativeMass z := by linarith
  have hpos := normalized_distance_margin (fun i => max (w i) 0)
    (fun i => max (z i) 0) (positiveMass w) (positiveMass z) μ
    (fun i => le_max_right _ _) pw pz rfl rfl hpw
  have hneg := normalized_distance_margin (fun i => max (-w i) 0)
    (fun i => max (-z i) 0) (negativeMass w) (negativeMass z) μ
    (fun i => le_max_right _ _) nw nz rfl rfl hnw
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    repair_point_distance w z pw nw pz nz i
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hsplit : l1Distance (fun i => max (w i) 0) (fun i => max (z i) 0) +
      l1Distance (fun i => max (-w i) 0) (fun i => max (-z i) 0) = l1Distance w z := by
    unfold l1Distance
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => parts_distance (w i) (z i)
  dsimp [l1Distance] at hpos hneg hsplit ⊢
  nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hμ)]

def encryptionProbability (c : Cipher Key) (message : Bool) (i : Key) : ℝ :=
  if message then c.enc1 i else c.enc0 i

/-- Total variation of the joint key/ciphertext laws for one fixed message.
This internal metric is not the advantage of an attacker who lacks the key. -/
def jointTV (c d : Cipher Key) (message : Bool) : ℝ :=
  (∑ i,
    (|c.weight i * encryptionProbability c message i -
      d.weight i * encryptionProbability d message i| +
    |c.weight i * (1 - encryptionProbability c message i) -
      d.weight i * (1 - encryptionProbability d message i)|)) / 2

def implementationDistance (c d : Cipher Key) : ℝ := max (jointTV c d false) (jointTV c d true)

theorem two_abs_contrast_le (a b c d : ℝ) (h : a + b = c + d) :
    2 * |a - c| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a - c| ≤ |a| + |c| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-c)
  have heq : a - c = d - b := by linarith
  have h2 : |a - c| ≤ |d| + |b| := by
    rw [heq]
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le d (-b)
  linarith

theorem contrast_distance_le_joint (c d : Cipher Key) :
    l1Distance (signedContrast c) (signedContrast d) ≤ jointTV c d false + jointTV c d true := by
  have hpoint (i : Key) := two_abs_contrast_le
    (c.weight i * c.enc0 i - d.weight i * d.enc0 i)
    (c.weight i * (1 - c.enc0 i) - d.weight i * (1 - d.enc0 i))
    (c.weight i * c.enc1 i - d.weight i * d.enc1 i)
    (c.weight i * (1 - c.enc1 i) - d.weight i * (1 - d.enc1 i)) (by ring)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  have heq (i : Key) :
      (c.weight i * c.enc0 i - d.weight i * d.enc0 i) -
      (c.weight i * c.enc1 i - d.weight i * d.enc1 i) =
      signedContrast c i - signedContrast d i := by unfold signedContrast; ring
  simp_rw [heq, Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  dsimp [l1Distance, jointTV, encryptionProbability]
  simp_rw [Finset.sum_add_distrib]
  linarith

theorem contrast_distance_le_implementation (c d : Cipher Key) :
    l1Distance (signedContrast c) (signedContrast d) ≤ 2 * implementationDistance c d := by
  have h := contrast_distance_le_joint c d
  have h0 : jointTV c d false ≤ implementationDistance c d := le_max_left _ _
  have h1 : jointTV c d true ≤ implementationDistance c d := le_max_right _ _
  linarith

theorem PerfectCipher.toCipher_other0 (d : PerfectCipher Key) (i : Key) :
    d.toCipher.weight i * (1 - d.toCipher.enc0 i) = max (-d.signed i) 0 := by
  have h : 1 - d.toCipher.enc0 i = d.toCipher.enc1 i := by
    dsimp [PerfectCipher.toCipher]
    split_ifs <;> norm_num
  rw [h]
  exact d.toCipher_weighted1 i

theorem PerfectCipher.toCipher_other1 (d : PerfectCipher Key) (i : Key) :
    d.toCipher.weight i * (1 - d.toCipher.enc1 i) = max (d.signed i) 0 := by
  have h : 1 - d.toCipher.enc1 i = d.toCipher.enc0 i := by
    dsimp [PerfectCipher.toCipher]
    split_ifs <;> norm_num
  rw [h]
  exact d.toCipher_weighted0 i

/-- Relates the signed-vector estimate to actual joint distributions. -/
theorem perfect_jointTV (c d : PerfectCipher Key) (message : Bool) :
    jointTV c.toCipher d.toCipher message = l1Distance c.signed d.signed / 2 := by
  cases message
  · simp only [jointTV, encryptionProbability, Bool.false_eq_true, ↓reduceIte,
      PerfectCipher.toCipher_weighted0, PerfectCipher.toCipher_other0, parts_distance, l1Distance]
  · simp only [jointTV, encryptionProbability, ↓reduceIte,
      PerfectCipher.toCipher_weighted1, PerfectCipher.toCipher_other1]
    simp_rw [add_comm (|max (-c.signed _) 0 - max (-d.signed _) 0|), parts_distance]
    rfl

/-- Quantitative repair theorem using only per-cipher privacy/correctness witnesses. -/
theorem repairedCipher_stable (c d : Cipher Key) (εc δc εd δd μ : ℝ) (hμ : 0 < μ)
    (hc0 : ∑ i, c.weight i * error0 c i ≤ δc)
    (hc1 : ∑ i, c.weight i * error1 c i ≤ δc)
    (hd0 : ∑ i, d.weight i * error0 d i ≤ δd)
    (hd1 : ∑ i, d.weight i * error1 d i ≤ δd)
    (hpc : |bias (signedContrast c)| ≤ εc)
    (hpd : |bias (signedContrast d)| ≤ εd)
    (hmc : εc + 2 * δc ≤ 1 - μ) (hmd : εd + 2 * δd ≤ 1 - μ) :
    ∃ outc outd : PerfectCipher Key,
      outc.signed = repair (signedContrast c) ∧
      outd.signed = repair (signedContrast d) ∧
      ∀ message, jointTV outc.toCipher outd.toCipher message ≤
        2 * implementationDistance c d / μ := by
  have hc := repair_margin_bound c εc δc μ hc0 hc1 hpc hmc
  have hd := repair_margin_bound d εd δd μ hd0 hd1 hpd hmd
  have pc : 0 < positiveMass (signedContrast c) := by linarith [hc.1]
  have nc : 0 < negativeMass (signedContrast c) := by linarith [hc.2]
  have pd : 0 < positiveMass (signedContrast d) := by linarith [hd.1]
  have nd : 0 < negativeMass (signedContrast d) := by linarith [hd.2]
  let outc : PerfectCipher Key := ⟨repair (signedContrast c), repair_bias _ pc nc, repair_mass _ pc nc⟩
  let outd : PerfectCipher Key := ⟨repair (signedContrast d), repair_bias _ pd nd, repair_mass _ pd nd⟩
  refine ⟨outc, outd, rfl, rfl, ?_⟩
  intro message
  rw [perfect_jointTV]
  apply (le_div_iff₀ hμ).mpr
  have hrepair := repair_distance_mul (signedContrast c) (signedContrast d) μ hμ hc.1 hc.2 hd.1 hd.2
  have hcontrast := contrast_distance_le_implementation c d
  change l1Distance (repair (signedContrast c)) (repair (signedContrast d)) / 2 * μ ≤ _
  nlinarith

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
