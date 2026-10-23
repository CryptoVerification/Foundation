import Foundation.Crypto.Semantics.Probability.ClassicalBitRepairStability

/-! Local four-point certificates for a mandatory jump of classical bit ciphers.
This file verifies a supplied zero-barycenter certificate. It does not extract
that certificate from a nonnull boundary or assert a cryptographic reduction
must preserve key labels and that boundary. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section
variable {Key : Type*} [Fintype Key]

theorem four_weights_large (α : Fin 4 → ℝ) (hs : ∑ i, α i = 1) :
    ∃ i, 1 / 4 ≤ α i := by
  by_contra h
  push Not at h
  have ht := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    Finset.univ_nonempty (fun i _ => h i)
  norm_num at ht
  linarith

/-- Any four unit l1 vectors whose nonnegative weighted mean is zero have
diameter at least 4/3. Zero weights and repeated vertices are allowed. -/
theorem unit_barycenter_diameter (v : Fin 4 → Key → ℝ) (α : Fin 4 → ℝ) (D : ℝ)
    (ha : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hu : ∀ i, mass (v i) = 1) (hz : ∀ k, ∑ i, α i * v i k = 0)
    (hD : ∀ i j, l1Distance (v i) (v j) ≤ D) : 4 / 3 ≤ D := by
  obtain ⟨i, hi⟩ := four_weights_large α hs
  have hnonneg : 0 ≤ D := by simpa [l1Distance] using hD i i
  have hpoint (k : Key) : |v i k| ≤ ∑ j, α j * |v i k - v j k| := by
    have heq : (∑ j, α j * (v i k - v j k)) = v i k := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, hz]
      ring
    calc
      _ = |∑ j, α j * (v i k - v j k)| := congrArg abs heq.symm
      _ ≤ ∑ j, |α j * (v i k - v j k)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (ha _)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun k _ => hpoint k
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  change mass (v i) ≤ ∑ j, α j * l1Distance (v i) (v j) at hsum
  rw [hu] at hsum
  have hterm (j : Fin 4) : α j * l1Distance (v i) (v j) ≤
      α j * D - (if j = i then α j * D else 0) := by
    by_cases hj : j = i
    · subst j
      simp [l1Distance]
    · simp only [hj, ↓reduceIte, sub_zero]
      exact mul_le_mul_of_nonneg_left (hD i j) (ha j)
  have hbound := Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs] at hbound
  simp only [one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hbound
  nlinarith [mul_le_mul_of_nonneg_right hi hnonneg]

theorem unit_barycenter_pair (v : Fin 4 → Key → ℝ) (α : Fin 4 → ℝ)
    (ha : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hu : ∀ i, mass (v i) = 1) (hz : ∀ k, ∑ i, α i * v i k = 0) :
    ∃ i j, 4 / 3 ≤ l1Distance (v i) (v j) := by
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Fin 4 × Fin 4 => l1Distance (v p.1) (v p.2)) Finset.univ_nonempty
  exact ⟨p.1, p.2, unit_barycenter_diameter v α _ ha hs hu hz
    (fun i j => hmax (i, j) (Finset.mem_univ _))⟩

/-- A local certificate yields a jump for actual joint key/ciphertext laws. -/
theorem perfect_simplex_jump (d : Fin 4 → PerfectCipher Key) (α : Fin 4 → ℝ)
    (ha : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hz : ∀ k, ∑ i, α i * (d i).signed k = 0) :
    ∃ i j, ∀ message, 2 / 3 ≤ jointTV (d i).toCipher (d j).toCipher message := by
  obtain ⟨i, j, hij⟩ := unit_barycenter_pair (fun i => (d i).signed) α ha hs
    (fun i => (d i).mass_one) hz
  refine ⟨i, j, fun message => ?_⟩
  rw [perfect_jointTV]
  linarith

/-- An approximate implementation with a zero-barycenter repair certificate
must already contain a large internal change. The hypotheses are local to four
implementations; existence of this certificate from a boundary is not assumed proved. -/
theorem approximate_simplex_jump (c : Fin 4 → Cipher Key) (ε δ : Fin 4 → ℝ)
    (μ : ℝ) (hμ : 0 < μ) (α : Fin 4 → ℝ)
    (ha : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (h0 : ∀ i, ∑ k, (c i).weight k * error0 (c i) k ≤ δ i)
    (h1 : ∀ i, ∑ k, (c i).weight k * error1 (c i) k ≤ δ i)
    (hp : ∀ i, |bias (signedContrast (c i))| ≤ ε i)
    (hm : ∀ i, ε i + 2 * δ i ≤ 1 - μ)
    (hz : ∀ k, ∑ i, α i * repair (signedContrast (c i)) k = 0) :
    ∃ i j, μ / 3 ≤ implementationDistance (c i) (c j) := by
  have hmargin (i : Fin 4) := repair_margin_bound (c i) (ε i) (δ i) μ
    (h0 i) (h1 i) (hp i) (hm i)
  have hmass (i : Fin 4) : mass (repair (signedContrast (c i))) = 1 := by
    apply repair_mass
    · linarith [(hmargin i).1]
    · linarith [(hmargin i).2]
  obtain ⟨i, j, hij⟩ := unit_barycenter_pair
    (fun i => repair (signedContrast (c i))) α ha hs hmass hz
  have hrepair := repair_distance_mul (signedContrast (c i)) (signedContrast (c j)) μ hμ
    (hmargin i).1 (hmargin i).2 (hmargin j).1 (hmargin j).2
  have hcontrast := contrast_distance_le_implementation (c i) (c j)
  refine ⟨i, j, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hij (le_of_lt hμ)]

/-- A concrete nonvacuous certificate attaining the exact four-point bound.
The probabilities include 1/6; this is not a bounded fair-coin implementation. -/
private theorem fin4_two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
private theorem fin4_three_ne_zero : (3 : Fin 4) ≠ 0 := by decide

def sharpTetrahedron (i : Fin 4) : PerfectCipher (Fin 4) where
  signed k := if k.val = i.val then -1 / 2 else 1 / 6
  bias_zero := by
    fin_cases i <;> norm_num [bias, Fin.sum_univ_four, fin4_two_ne_zero, fin4_three_ne_zero]
  mass_one := by
    fin_cases i <;> norm_num [mass, Fin.sum_univ_four, fin4_two_ne_zero, fin4_three_ne_zero]

theorem sharpTetrahedron_barycenter (k : Fin 4) :
    (∑ i : Fin 4, (1 / 4 : ℝ) * (sharpTetrahedron i).signed k) = 0 := by
  fin_cases k <;> norm_num [sharpTetrahedron, Fin.sum_univ_four, fin4_two_ne_zero, fin4_three_ne_zero]

theorem sharpTetrahedron_joint_bound (i j : Fin 4) (message : Bool) :
    jointTV (sharpTetrahedron i).toCipher (sharpTetrahedron j).toCipher message ≤ 2 / 3 := by
  rw [perfect_jointTV]
  fin_cases i <;> fin_cases j <;>
    norm_num [l1Distance, sharpTetrahedron, Fin.sum_univ_four, fin4_two_ne_zero, fin4_three_ne_zero]

theorem sharpTetrahedron_attains :
    ∃ i j, ∀ message, jointTV (sharpTetrahedron i).toCipher
      (sharpTetrahedron j).toCipher message = 2 / 3 := by
  obtain ⟨i, j, hij⟩ := perfect_simplex_jump sharpTetrahedron (fun _ => (1 / 4 : ℝ))
    (by intro i; norm_num) (by norm_num [Fin.sum_univ_four]) sharpTetrahedron_barycenter
  exact ⟨i, j, fun message => le_antisymm (sharpTetrahedron_joint_bound i j message) (hij message)⟩

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
