import Foundation.Crypto.Semantics.Probability.GeneralKernelVariation

/-! Finite compatibility, arbitrary probabilistic observers, and retained-input
joint laws for total variation on arbitrary discrete state types. -/
namespace Foundation.Probability.GeneralKernelVariation
open scoped BigOperators ENNReal
noncomputable section
variable {A B C : Type}

theorem variation_finite_eq [Fintype A] (p q : PMF A) :
    variation p q = ENNReal.ofReal (finiteVariation p q) := by
  unfold variation finiteVariation
  rw [tsum_fintype,ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  have two : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [two,div_eq_mul_inv,mul_comm]

theorem distance_finite_eq [Fintype A] [Fintype B] (p : PMF A) (f g : A → PMF B) :
    distance p f g = ENNReal.ofReal (FiniteKernelVariation.distance p f g) := by
  unfold distance FiniteKernelVariation.distance
  rw [tsum_fintype,ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (FiniteKernelVariation.variation_nonneg _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [variation_finite_eq,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (p.apply_ne_top a)]

theorem map_contraction (p q : PMF A) (emit : A → B) : variation (p.map emit) (q.map emit) ≤ variation p q :=
  postprocess p q (fun a => PMF.pure (emit a))

theorem map_isometry (p q : PMF A) (emit : A → B) (read : B → A) (inverse : Function.LeftInverse read emit) :
    variation (p.map emit) (q.map emit) = variation p q := by
  have recover (law : PMF A) : (law.map emit).map read = law := by
    rw [PMF.map_comp,show read ∘ emit = id from funext inverse,PMF.map_id]
  exact le_antisymm (map_contraction p q emit)
    (by simpa only [recover] using map_contraction (p.map emit) (q.map emit) read)

theorem event_bound (p q : PMF A) (event : A → Prop) : probabilityGap (eventProb p event) (eventProb q event) ≤ variation p q := by
  classical
  let bit (a : A) : Bool := decide (event a)
  have law (p : PMF A) : eventProb (p.map bit) (· = true) = eventProb p event := by
    rw [eventProb_map]
    congr 1
    funext a
    simp [bit]
  have finite := probabilistic_event_bound (p.map bit) (q.map bit) PMF.pure (· = true)
  simp only [PMF.bind_pure] at finite
  rw [← variation_finite_eq,law p,law q] at finite
  exact finite.trans (map_contraction p q bit)

theorem probabilistic_event_bound (p q : PMF A) (next : A → PMF B) (event : B → Prop) :
    probabilityGap (eventProb (p.bind next) event) (eventProb (q.bind next) event) ≤ variation p q :=
  (event_bound _ _ event).trans (postprocess p q next)

theorem all_observers_bound (p q : PMF A) : ObserverBound (fun _ => True) p q (variation p q) := by
  intro observer _
  exact probabilistic_event_bound p q observer (· = true)

def joint (p : PMF A) (f : A → PMF B) : PMF (A × B) := p.bind (fun a => (f a).map (fun b => (a,b)))

theorem joint_apply (p : PMF A) (f : A → PMF B) (a : A) (b : B) : joint p f (a,b) = p a * f a b := by
  classical
  unfold joint
  rw [PMF.bind_apply,tsum_eq_single a]
  · rw [PMF.map_apply,tsum_eq_single b]
    · simp
    · intro other different
      simp [Ne.symm different]
  · intro other different
    have zero : ((f other).map (fun y => (other,y))) (a,b) = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro y
      simp [Ne.symm different]
    rw [zero,mul_zero]

theorem joint_variation (p : PMF A) (f g : A → PMF B) : variation (joint p f) (joint p g) = distance p f g := by
  unfold variation
  rw [ENNReal.tsum_prod']
  simp only [joint_apply,ENNReal.toReal_mul,← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
  have factor (a : A) (b : B) : ENNReal.ofReal ((p a).toReal * |(f a b).toReal - (g a b).toReal|) =
      p a * ENNReal.ofReal |(f a b).toReal - (g a b).toReal| := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (p.apply_ne_top a)]
  simp_rw [factor,ENNReal.tsum_mul_left]
  unfold distance variation
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr (fun a => mul_left_comm _ _ _)

theorem map_average (p : PMF A) (emit : A → B) (weight : B → ℝ≥0∞) :
    (∑' b, (p.map emit) b * weight b) = ∑' a, p a * weight (emit a) := by
  change (∑' b, (p.bind (fun a => PMF.pure (emit a))) b * weight b) = _
  rw [bind_average]
  simp [PMF.pure_apply,ite_mul]

theorem mapped_distance (p : PMF A) (emit : A → B) (f g : B → PMF C) :
    distance (p.map emit) f g = ∑' a, p a * variation (f (emit a)) (g (emit a)) := map_average p emit _

theorem joint_observer_bound (p : PMF A) (f g : A → PMF B) (observer : A × B → PMF C) (event : C → Prop) :
    probabilityGap (eventProb ((joint p f).bind observer) event) (eventProb ((joint p g).bind observer) event) ≤ distance p f g := by
  rw [← joint_variation]
  exact probabilistic_event_bound _ _ observer event

end
end Foundation.Probability.GeneralKernelVariation
