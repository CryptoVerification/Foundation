import Foundation.Quantum.PartialTrace

/-! A coherent attack on one transmitted BB84 qubit. The environment is
retained, not measured away. Exact zero-disturbance is a lemma for the eventual
finite-error sampling proof, not a finite-key security theorem. -/
namespace Foundation.Quantum.QKD
open scoped ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure BB84Attack (e : Space) where
  dilation : Op .bit (.tensor .bit e)
  isometry : dilation.conjTranspose * dilation = 1

namespace BB84Attack
variable {e : Space}

/-- In the computational basis the two wrong-output amplitudes vanish. -/
def zeroZ (V : BB84Attack e) : Prop :=
  ∀ u : e.Basis, V.dilation (1, u) 0 = 0 ∧ V.dilation (0, u) 1 = 0

/-- The plus input has zero amplitude in the minus output.
The common nonzero normalization factor cancels in this equality. -/
def zeroX (V : BB84Attack e) : Prop :=
  ∀ u : e.Basis, V.dilation (0, u) 0 + V.dilation (0, u) 1 =
    V.dilation (1, u) 0 + V.dilation (1, u) 1

/-- Squared amplitude of a computational-basis error for a specified input. -/
def zError (V : BB84Attack e) (b : Fin 2) : ℝ :=
  ∑ u : e.Basis, Complex.normSq (V.dilation (1 - b, u) b)

/-- Squared minus-output amplitude for a plus input, including both normalization factors. -/
def xPlusError (V : BB84Attack e) : ℝ :=
  (∑ u : e.Basis, Complex.normSq
    (V.dilation (0, u) 0 + V.dilation (0, u) 1 -
      V.dilation (1, u) 0 - V.dilation (1, u) 1)) / 4

theorem zeroZ_of_errors (V : BB84Attack e) (h0 : V.zError 0 = 0) (h1 : V.zError 1 = 0) :
    V.zeroZ := by
  have hsum0 : ∑ u : e.Basis, Complex.normSq (V.dilation (1, u) 0) = 0 := by
    simpa [zError] using h0
  have hsum1 : ∑ u : e.Basis, Complex.normSq (V.dilation (0, u) 1) = 0 := by
    simpa [zError] using h1
  have hz0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u (_ : u ∈ Finset.univ) => Complex.normSq_nonneg (V.dilation (1, u) 0))).mp hsum0
  have hz1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u (_ : u ∈ Finset.univ) => Complex.normSq_nonneg (V.dilation (0, u) 1))).mp hsum1
  intro u
  exact ⟨Complex.normSq_eq_zero.mp (hz0 u (Finset.mem_univ u)),
    Complex.normSq_eq_zero.mp (hz1 u (Finset.mem_univ u))⟩

theorem zeroX_of_error (V : BB84Attack e) (hx : V.xPlusError = 0) : V.zeroX := by
  have hsum : ∑ u : e.Basis, Complex.normSq
      (V.dilation (0, u) 0 + V.dilation (0, u) 1 -
        V.dilation (1, u) 0 - V.dilation (1, u) 1) = 0 := by
    simpa only [xPlusError, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hx
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u (_ : u ∈ Finset.univ) => Complex.normSq_nonneg
      (V.dilation (0, u) 0 + V.dilation (0, u) 1 -
        V.dilation (1, u) 0 - V.dilation (1, u) 1))).mp hsum
  intro u
  have he := Complex.normSq_eq_zero.mp (hz u (Finset.mem_univ u))
  change V.dilation (0, u) 0 + V.dilation (0, u) 1 =
    V.dilation (1, u) 0 + V.dilation (1, u) 1
  linear_combination he

/-- Both complementary tests force the same environmental vector for either key bit. -/
theorem factorization (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX)
    (i j : Fin 2) (u : e.Basis) :
    V.dilation (i, u) j = if i = j then V.dilation (0, u) 0 else 0 := by
  have hx := hX u
  obtain ⟨hz10, hz01⟩ := hZ u
  simp only [hz10, hz01, add_zero, zero_add] at hx
  fin_cases i <;> fin_cases j <;> simp_all

/-- The environmental state is normalized because the dilation is an isometry. -/
theorem environment_normalized (V : BB84Attack e) (hZ : V.zeroZ) :
    ∑ u : e.Basis, star (V.dilation (0, u) 0) * V.dilation (0, u) 0 = 1 := by
  have h := congrFun (congrFun V.isometry (0 : Fin 2)) (0 : Fin 2)
  change (∑ p : Fin 2 × e.Basis, star (V.dilation p 0) * V.dilation p 0) = 1 at h
  simp_rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simpa only [(hZ _).1, star_zero, zero_mul, Finset.sum_const_zero, add_zero] using h

/-- Unnormalized environmental matrix conditional on a computational input bit. -/
def environmentMatrix (V : BB84Attack e) (b : Fin 2) : Operator e :=
  fun u v => ∑ i : Fin 2, V.dilation (i, u) b * star (V.dilation (i, v) b)

/-- The reduced environment is a positive matrix for every input bit and every attack. -/
theorem environment_positive (V : BB84Attack e) (b : Fin 2) :
    (V.environmentMatrix b).PosSemidef := by
  let M : Matrix (Fin 2) e.Basis ℂ := fun i u => star (V.dilation (i, u) b)
  have he : V.environmentMatrix b = M.conjTranspose * M := by
    ext u v
    simp [environmentMatrix, M, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self M

theorem environment_trace (V : BB84Attack e) (b : Fin 2) :
    (V.environmentMatrix b).trace = 1 := by
  have h := congrFun (congrFun V.isometry b) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ite_true] at h
  change (∑ u : e.Basis, ∑ i : Fin 2, V.dilation (i, u) b * star (V.dilation (i, u) b)) = 1
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type, mul_comm] using h

/-- The attacker's retained subsystem is an actual normalized density operator. -/
def environmentState (V : BB84Attack e) (b : Fin 2) : Density e where
  matrix := V.environmentMatrix b
  positive := V.environment_positive b
  normalized := V.environment_trace b

theorem environment_factor (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX)
    (b : Fin 2) (u v : e.Basis) :
    V.environmentMatrix b u v = V.dilation (0, u) 0 * star (V.dilation (0, v) 0) := by
  change (∑ i : Fin 2, V.dilation (i, u) b * star (V.dilation (i, v) b)) = _
  calc
    _ = ∑ i : Fin 2, (if i = b then V.dilation (0, u) 0 else 0) *
        star (if i = b then V.dilation (0, v) 0 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [V.factorization hZ hX i b u, V.factorization hZ hX i b v]
    _ = _ := by simp [apply_ite]

/-- The environment has no information about the key in the exact test case. -/
theorem environment_independent (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX)
    (b c : Fin 2) : V.environmentMatrix b = V.environmentMatrix c := by
  ext u v
  rw [V.environment_factor hZ hX, V.environment_factor hZ hX]

/-- Every two-outcome measurement of the retained system has the same acceptance probability. -/
theorem environment_test_independent (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX)
    (E : Effect e) (b c : Fin 2) :
    E.probability (V.environmentState b) = E.probability (V.environmentState c) := by
  change (E.matrix * V.environmentMatrix b).trace.re =
    (E.matrix * V.environmentMatrix c).trace.re
  rw [V.environment_independent hZ hX b c]

/-- A quantitative amplitude bound, without assuming either test is exact. -/
theorem environment_amplitude_bound (V : BB84Attack e) (u : e.Basis) :
    ‖V.dilation (0, u) 0 - V.dilation (1, u) 1‖ ≤
      ‖V.dilation (0, u) 0 + V.dilation (0, u) 1 -
        V.dilation (1, u) 0 - V.dilation (1, u) 1‖ +
      (‖V.dilation (1, u) 0‖ + ‖V.dilation (0, u) 1‖) := by
  calc
    _ = ‖(V.dilation (0, u) 0 + V.dilation (0, u) 1 -
        V.dilation (1, u) 0 - V.dilation (1, u) 1) +
        (V.dilation (1, u) 0 - V.dilation (0, u) 1)‖ := by congr 1; ring
    _ ≤ ‖V.dilation (0, u) 0 + V.dilation (0, u) 1 -
        V.dilation (1, u) 0 - V.dilation (1, u) 1‖ +
        ‖V.dilation (1, u) 0 - V.dilation (0, u) 1‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl
      (norm_sub_le (V.dilation (1, u) 0) (V.dilation (0, u) 1))

end BB84Attack
end
end Foundation.Quantum.QKD
