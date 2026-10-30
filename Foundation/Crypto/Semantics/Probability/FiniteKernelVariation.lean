import Foundation.Crypto.Semantics.Probability.FiniteObserverVariation

/-! Source-weighted total variation of finite conditional kernels. Common
postprocessing contracts distance; a preserving prefix transports the source
weight. These bounds support approximate comparisons in sequential contexts. -/
namespace Foundation.Probability.FiniteKernelVariation
open scoped BigOperators ENNReal
noncomputable section
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem singleton {T : Type} (p : PMF T) (a : T) : eventProb p (· = a) = p a :=
  PMF.toOuterMeasure_apply_singleton p a

omit [Fintype B] [Fintype C] in
theorem variation_nonneg (p q : PMF A) : 0 ≤ finiteVariation p q :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

omit [Fintype B] [Fintype C] in
theorem variation_self (p : PMF A) : finiteVariation p p = 0 := by simp [finiteVariation]

omit [Fintype B] [Fintype C] in
theorem variation_symm (p q : PMF A) : finiteVariation p q = finiteVariation q p := by
  unfold finiteVariation
  exact congrArg (fun r : ℝ => r / 2) (Finset.sum_congr rfl (fun a _ => abs_sub_comm _ _))

omit [Fintype B] [Fintype C] in
theorem variation_triangle (p q r : PMF A) :
    finiteVariation p r ≤ finiteVariation p q + finiteVariation q r := by
  have h : (∑ a, |(p a).toReal - (r a).toReal|) ≤
      (∑ a, |(p a).toReal - (q a).toReal|) + ∑ a, |(q a).toReal - (r a).toReal| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun a _ => abs_sub_le _ _ _)
  unfold finiteVariation
  linarith

omit [Fintype B] [Fintype C] in
theorem variation_zero_iff (p q : PMF A) : finiteVariation p q = 0 ↔ p = q := by
  constructor
  · intro h
    have sum_zero : (∑ a, |(p a).toReal - (q a).toReal|) = 0 := by
      unfold finiteVariation at h
      linarith
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) =>
      abs_nonneg ((p a).toReal - (q a).toReal))).mp sum_zero
    ext a
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
    exact sub_eq_zero.mp (abs_eq_zero.mp (each a (Finset.mem_univ a)))
  · rintro rfl
    exact variation_self p

omit [Fintype B] [Fintype C] in
theorem variation_pure (p : PMF A) (a : A) : finiteVariation p (PMF.pure a) = 1 - (p a).toReal := by
  classical
  have pa : (p a).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one a)
  have term (x : A) : |(p x).toReal - (PMF.pure a x).toReal| =
      (p x).toReal + if x = a then 1 - 2 * (p a).toReal else 0 := by
    by_cases same : x = a
    · subst x
      simp only [PMF.pure_apply_self, ENNReal.toReal_one, if_true, abs_of_nonpos (by linarith : (p a).toReal - 1 ≤ 0)]
      ring
    · simp [PMF.pure_apply, same, abs_of_nonneg ENNReal.toReal_nonneg]
  unfold finiteVariation
  simp_rw [term]
  rw [Finset.sum_add_distrib, sum_real_mass]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [Fintype B] [Fintype C] in
theorem bind_real (p : PMF A) (kernel : A → PMF B) (b : B) :
    ((p.bind kernel) b).toReal = ∑ a, (p a).toReal * (kernel a b).toReal := by
  simpa only [singleton] using event_bind_real p kernel (· = b)

def distance (p : PMF A) (f g : A → PMF B) : ℝ := ∑ a, (p a).toReal * finiteVariation (f a) (g a)

omit [Fintype C] in
theorem nonneg (p : PMF A) (f g : A → PMF B) : 0 ≤ distance p f g :=
  Finset.sum_nonneg (fun _a _ => mul_nonneg ENNReal.toReal_nonneg (variation_nonneg _ _))

omit [Fintype C] in
theorem self (p : PMF A) (f : A → PMF B) : distance p f f = 0 := by simp [distance, variation_self]

omit [Fintype C] in
theorem symm (p : PMF A) (f g : A → PMF B) : distance p f g = distance p g f := by
  unfold distance
  exact Finset.sum_congr rfl (fun a _ => congrArg ((p a).toReal * ·) (variation_symm _ _))

omit [Fintype C] in
theorem triangle (p : PMF A) (f g h : A → PMF B) : distance p f h ≤ distance p f g + distance p g h := by
  unfold distance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a _ => by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (variation_triangle _ _ _) ENNReal.toReal_nonneg)

omit [Fintype C] in
theorem zero_on_support (p : PMF A) (f g : A → PMF B) (zero : distance p f g = 0) :
    ∀ a ∈ p.support, f a = g a := by
  intro a supported
  have term := (Finset.sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ Finset.univ) =>
    mul_nonneg ENNReal.toReal_nonneg (variation_nonneg (f x) (g x)))).mp zero a (Finset.mem_univ a)
  have positive : (p a).toReal ≠ 0 := by
    intro h
    have hp := (ENNReal.toReal_eq_zero_iff _).mp h
    exact (PMF.mem_support_iff _ _).mp supported (hp.resolve_right (p.apply_ne_top a))
  exact (variation_zero_iff _ _).mp ((mul_eq_zero.mp term).resolve_left positive)

omit [Fintype C] in
theorem mixture (p : PMF A) (f g : A → PMF B) :
    finiteVariation (p.bind f) (p.bind g) ≤ distance p f g := by
  have bound : (∑ b, |∑ a, (p a).toReal * ((f a b).toReal - (g a b).toReal)|) ≤
      ∑ b, ∑ a, (p a).toReal * |(f a b).toReal - (g a b).toReal| := by
    apply Finset.sum_le_sum
    intro b _
    calc
      _ ≤ ∑ a, |(p a).toReal * ((f a b).toReal - (g a b).toReal)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  unfold finiteVariation
  simp_rw [bind_real, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ (∑ b, ∑ a, (p a).toReal * |(f a b).toReal - (g a b).toReal|) / 2 := by linarith
    _ = distance p f g := by
      rw [Finset.sum_comm]
      simp only [distance, finiteVariation, Finset.mul_sum, Finset.sum_div, mul_div_assoc]

theorem postprocess (p q : PMF B) (kernel : B → PMF C) :
    finiteVariation (p.bind kernel) (q.bind kernel) ≤ finiteVariation p q := by
  have bound : (∑ c, |∑ b, ((p b).toReal - (q b).toReal) * (kernel b c).toReal|) ≤
      ∑ c, ∑ b, |(p b).toReal - (q b).toReal| * (kernel b c).toReal := by
    apply Finset.sum_le_sum
    intro c _
    calc
      _ ≤ ∑ b, |((p b).toReal - (q b).toReal) * (kernel b c).toReal| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [Finset.sum_comm] at bound
  simp only [← Finset.mul_sum, sum_real_mass, mul_one] at bound
  unfold finiteVariation
  simp_rw [bind_real, ← Finset.sum_sub_distrib, ← sub_mul]
  linarith

theorem post (p : PMF A) (f g : A → PMF B) (kernel : B → PMF C) :
    distance p (fun a => (f a).bind kernel) (fun a => (g a).bind kernel) ≤ distance p f g := by
  exact Finset.sum_le_sum (fun a _ =>
    mul_le_mul_of_nonneg_left (postprocess (f a) (g a) kernel) ENNReal.toReal_nonneg)

theorem pre (p : PMF A) (q : PMF B) (kernel : A → PMF B) (f g : B → PMF C)
    (preserve : p.bind kernel = q) :
    distance p (fun a => (kernel a).bind f) (fun a => (kernel a).bind g) ≤ distance q f g := by
  calc
    _ ≤ ∑ a, (p a).toReal * distance (kernel a) f g := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (mixture (kernel a) f g) ENNReal.toReal_nonneg)
    _ = distance q f g := by
      simp only [distance, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_mul, ← bind_real, preserve]

theorem seq (p : PMF A) (q : PMF B) (f f' : A → PMF B) (g g' : B → PMF C)
    (preserve : p.bind f' = q) :
    distance p (fun a => (f a).bind g) (fun a => (f' a).bind g') ≤
      distance p f f' + distance q g g' := by
  exact (triangle p _ (fun a => (f' a).bind g) _).trans
    (add_le_add (post p f f' g) (pre p q f' g g' preserve))

end
end Foundation.Probability.FiniteKernelVariation
