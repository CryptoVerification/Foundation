import Foundation.Crypto.Semantics.Probability.FiniteKernelVariation
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Total variation and input-weighted kernel discrepancy for PMFs on arbitrary
state types. No finite or countable typeclass is required; finite probability
mass controls convergence. Extended nonnegative budgets avoid subtraction at
infinity. This concerns discrete PMFs, not arbitrary continuous measures. -/
namespace Foundation.Probability.GeneralKernelVariation
open scoped BigOperators ENNReal
noncomputable section
variable {A B C : Type}

def variation (p q : PMF A) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∑' a, ENNReal.ofReal |(p a).toReal - (q a).toReal|

def distance (p : PMF A) (f g : A → PMF B) : ℝ≥0∞ := ∑' a, p a * variation (f a) (g a)

theorem variation_self (p : PMF A) : variation p p = 0 := by simp [variation]

theorem variation_symm (p q : PMF A) : variation p q = variation q p := by
  unfold variation
  simp_rw [abs_sub_comm]

theorem variation_triangle (p q r : PMF A) : variation p r ≤ variation p q + variation q r := by
  unfold variation
  rw [← mul_add,← ENNReal.tsum_add]
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro a
  exact (ENNReal.ofReal_le_ofReal (abs_sub_le (p a).toReal (q a).toReal (r a).toReal)).trans_eq
    (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))

theorem variation_le_one (p q : PMF A) : variation p q ≤ 1 := by
  have term (a : A) : ENNReal.ofReal |(p a).toReal - (q a).toReal| ≤ p a + q a := by
    have bound : |(p a).toReal - (q a).toReal| ≤ (p a).toReal + (q a).toReal := by
      exact abs_le.mpr ⟨by linarith [(show (0 : ℝ) ≤ (p a).toReal from ENNReal.toReal_nonneg)], by linarith [(show (0 : ℝ) ≤ (q a).toReal from ENNReal.toReal_nonneg)]⟩
    have h := ENNReal.ofReal_le_ofReal bound
    simpa only [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (p.apply_ne_top a),ENNReal.ofReal_toReal (q.apply_ne_top a)] using h
  calc
    variation p q ≤ (2 : ℝ≥0∞)⁻¹ * ∑' a, (p a + q a) := mul_le_mul_right (ENNReal.tsum_le_tsum term) _
    _ = 1 := by
      rw [ENNReal.tsum_add,p.tsum_coe,q.tsum_coe,one_add_one_eq_two]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem variation_ne_top (p q : PMF A) : variation p q ≠ ∞ := ne_of_lt ((variation_le_one p q).trans_lt (by simp))

theorem variation_zero_iff (p q : PMF A) : variation p q = 0 ↔ p = q := by
  constructor
  · intro zero
    have sumzero : (∑' a, ENNReal.ofReal |(p a).toReal - (q a).toReal|) = 0 := by
      have h := (mul_eq_zero.mp zero).resolve_left (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)
      exact h
    ext a
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
    have term := ENNReal.tsum_eq_zero.mp sumzero a
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp term) (abs_nonneg _)))
  · rintro rfl
    exact variation_self p

/- Absolute convergence is obtained from finite total mass on both sides. -/
theorem sum_difference_bound (u v : A → ℝ≥0∞) (hu : ∑' a, u a ≠ ∞) (hv : ∑' a, v a ≠ ∞) :
    ENNReal.ofReal |(∑' a, u a).toReal - (∑' a, v a).toReal| ≤
      ∑' a, ENNReal.ofReal |(u a).toReal - (v a).toReal| := by
  have us := ENNReal.summable_toReal hu
  have vs := ENNReal.summable_toReal hv
  have ds := (us.sub vs).abs
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hu),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hv),← us.tsum_sub vs]
  have bound : |(∑' a, ((u a).toReal - (v a).toReal))| ≤ ∑' a, |(u a).toReal - (v a).toReal| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun a => (u a).toReal - (v a).toReal) (by simpa only [Real.norm_eq_abs] using ds)
  exact (ENNReal.ofReal_le_ofReal bound).trans_eq (ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) ds)

theorem postprocess (p q : PMF A) (next : A → PMF B) :
    variation (p.bind next) (q.bind next) ≤ variation p q := by
  have term (b : B) : ENNReal.ofReal |((p.bind next) b).toReal - ((q.bind next) b).toReal| ≤
      ∑' a, ENNReal.ofReal |(p a).toReal - (q a).toReal| * next a b := by
    have h := sum_difference_bound (fun a => p a * next a b) (fun a => q a * next a b)
      (by rw [← PMF.bind_apply]; exact (p.bind next).apply_ne_top b)
      (by rw [← PMF.bind_apply]; exact (q.bind next).apply_ne_top b)
    simp only [← PMF.bind_apply] at h
    have factor (a : A) : ENNReal.ofReal |(p a * next a b).toReal - (q a * next a b).toReal| =
        ENNReal.ofReal |(p a).toReal - (q a).toReal| * next a b := by
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul,← sub_mul,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_toReal ((next a).apply_ne_top b)]
    simp_rw [factor] at h
    exact h
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∑' b, ∑' a, ENNReal.ofReal |(p a).toReal - (q a).toReal| * next a b :=
      mul_le_mul_right (ENNReal.tsum_le_tsum term) _
    _ = (2 : ℝ≥0∞)⁻¹ * ∑' a, ∑' b, ENNReal.ofReal |(p a).toReal - (q a).toReal| * next a b :=
      congrArg ((2 : ℝ≥0∞)⁻¹ * ·) ENNReal.tsum_comm
    _ = variation p q := by simp only [ENNReal.tsum_mul_left,PMF.tsum_coe,mul_one,variation]

theorem mixture (p : PMF A) (f g : A → PMF B) : variation (p.bind f) (p.bind g) ≤ distance p f g := by
  have term (b : B) : ENNReal.ofReal |((p.bind f) b).toReal - ((p.bind g) b).toReal| ≤
      ∑' a, p a * ENNReal.ofReal |(f a b).toReal - (g a b).toReal| := by
    have h := sum_difference_bound (fun a => p a * f a b) (fun a => p a * g a b)
      (by rw [← PMF.bind_apply]; exact (p.bind f).apply_ne_top b)
      (by rw [← PMF.bind_apply]; exact (p.bind g).apply_ne_top b)
    simp only [← PMF.bind_apply] at h
    have factor (a : A) : ENNReal.ofReal |(p a * f a b).toReal - (p a * g a b).toReal| =
        p a * ENNReal.ofReal |(f a b).toReal - (g a b).toReal| := by
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul,← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (p.apply_ne_top a)]
    simp_rw [factor] at h
    exact h
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∑' b, ∑' a, p a * ENNReal.ofReal |(f a b).toReal - (g a b).toReal| :=
      mul_le_mul_right (ENNReal.tsum_le_tsum term) _
    _ = (2 : ℝ≥0∞)⁻¹ * ∑' a, ∑' b, p a * ENNReal.ofReal |(f a b).toReal - (g a b).toReal| :=
      congrArg ((2 : ℝ≥0∞)⁻¹ * ·) ENNReal.tsum_comm
    _ = distance p f g := by
      simp only [ENNReal.tsum_mul_left,distance,variation]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      exact mul_left_comm _ _ _

theorem self (p : PMF A) (f : A → PMF B) : distance p f f = 0 := by simp [distance,variation_self]

theorem symm (p : PMF A) (f g : A → PMF B) : distance p f g = distance p g f := by simp_rw [distance,variation_symm]

theorem triangle (p : PMF A) (f g h : A → PMF B) : distance p f h ≤ distance p f g + distance p g h := by
  rw [distance,distance,distance,← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (fun a => (mul_le_mul_right (variation_triangle (f a) (g a) (h a)) (p a)).trans_eq (mul_add _ _ _))

theorem le_one (p : PMF A) (f g : A → PMF B) : distance p f g ≤ 1 := by
  calc
    _ ≤ ∑' a, p a * 1 := ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (variation_le_one (f a) (g a)) _)
    _ = 1 := by simp [PMF.tsum_coe]

theorem zero_on_support (p : PMF A) (f g : A → PMF B) (zero : distance p f g = 0) (a : A) (supported : a ∈ p.support) : f a = g a := by
  have term := ENNReal.tsum_eq_zero.mp zero a
  exact (variation_zero_iff _ _).mp ((mul_eq_zero.mp term).resolve_left ((PMF.mem_support_iff _ _).mp supported))

theorem post (p : PMF A) (f g : A → PMF B) (next : B → PMF C) :
    distance p (fun a => (f a).bind next) (fun a => (g a).bind next) ≤ distance p f g :=
  ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (postprocess (f a) (g a) next) _)

theorem bind_average (p : PMF A) (next : A → PMF B) (weight : B → ℝ≥0∞) :
    (∑' b, (p.bind next) b * weight b) = ∑' a, p a * ∑' b, next a b * weight b := by
  simp_rw [PMF.bind_apply,← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc,ENNReal.tsum_mul_left]

theorem pre (p : PMF A) (q : PMF B) (next : A → PMF B) (f g : B → PMF C) (preserve : p.bind next = q) :
    distance p (fun a => (next a).bind f) (fun a => (next a).bind g) ≤ distance q f g := by
  calc
    _ ≤ ∑' a, p a * distance (next a) f g := ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (mixture (next a) f g) _)
    _ = distance q f g := by
      change (∑' a, p a * ∑' b, next a b * variation (f b) (g b)) = ∑' b, q b * variation (f b) (g b)
      rw [← bind_average,preserve]

theorem seq (p : PMF A) (q : PMF B) (f f' : A → PMF B) (g g' : B → PMF C) (preserve : p.bind f' = q) :
    distance p (fun a => (f a).bind g) (fun a => (f' a).bind g') ≤ distance p f f' + distance q g g' :=
  (triangle p _ (fun a => (f' a).bind g) _).trans (add_le_add (post p f f' g) (pre p q f' g g' preserve))

end
end Foundation.Probability.GeneralKernelVariation
