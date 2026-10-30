import Foundation.Crypto.Semantics.Probability.FiniteVariationWitness
import Foundation.Crypto.Semantics.Probability.FiniteMaximalKernel

/-! Quantitative recovery for finite stochastic kernels. Randomized reverse
kernels cannot beat the best deterministic decoder for a fixed joint law.
Row and column capacities then give a bound uniform over all forward kernels. -/
namespace Foundation.Probability.FiniteRecoveryError
open scoped BigOperators ENNReal
noncomputable section
variable {A B : Type} [Fintype A] [Nonempty A] [Fintype B]
local instance : DecidableEq A := Classical.decEq A

def capacity (p : A → ℝ) (q : B → ℝ) (decoder : B → A) : ℝ :=
  ∑ a, min (p a) (∑ b, if decoder b = a then q b else 0)

theorem deterministic_dominates (mass : A → B → ℝ) (reverse : B → A → ℝ)
    (nonneg : ∀ b a, 0 ≤ reverse b a) (normalized : ∀ b, ∑ a, reverse b a = 1) :
    ∃ decoder : B → A, (∑ a, ∑ b, mass a b * reverse b a) ≤ ∑ b, mass (decoder b) b := by
  classical
  have maxima (b : B) : ∃ a, ∀ x, mass x b ≤ mass a b := by
    obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ (fun a => mass a b) Finset.univ_nonempty
    exact ⟨a,fun x => ha x (Finset.mem_univ x)⟩
  choose decoder best using maxima
  refine ⟨decoder,?_⟩
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _
  calc
    _ ≤ ∑ a, mass (decoder b) b * reverse b a := Finset.sum_le_sum
      (fun a _ => mul_le_mul_of_nonneg_right (best b a) (nonneg b a))
    _ = mass (decoder b) b := by rw [← Finset.mul_sum, normalized, mul_one]

omit [Nonempty A] in
theorem deterministic_capacity (mass : A → B → ℝ) (p : A → ℝ) (q : B → ℝ)
    (nonneg : ∀ a b, 0 ≤ mass a b) (rows : ∀ a, ∑ b, mass a b = p a)
    (cols : ∀ b, ∑ a, mass a b = q b) (decoder : B → A) :
    (∑ b, mass (decoder b) b) ≤ capacity p q decoder := by
  classical
  have selected (a : A) : (∑ b, if decoder b = a then mass a b else 0) ≤
      min (p a) (∑ b, if decoder b = a then q b else 0) := by
    apply le_min
    · rw [← rows a]
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · rfl
      · exact nonneg a b
    · apply Finset.sum_le_sum
      intro b _
      split_ifs
      · rw [← cols b]
        exact Finset.single_le_sum (fun a _ => nonneg a b) (Finset.mem_univ a)
      · rfl
  have total : (∑ a, ∑ b, if decoder b = a then mass a b else 0) = ∑ b, mass (decoder b) b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp
  rw [← total]
  exact Finset.sum_le_sum (fun a _ => selected a)

theorem matrix_success_bound (mass : A → B → ℝ) (p : A → ℝ) (q : B → ℝ)
    (reverse : B → A → ℝ) (nonneg : ∀ a b, 0 ≤ mass a b)
    (rows : ∀ a, ∑ b, mass a b = p a) (cols : ∀ b, ∑ a, mass a b = q b)
    (reverse_nonneg : ∀ b a, 0 ≤ reverse b a) (reverse_sum : ∀ b, ∑ a, reverse b a = 1)
    (bound : ℝ) (all_decoders : ∀ decoder, capacity p q decoder ≤ bound) :
    (∑ a, ∑ b, mass a b * reverse b a) ≤ bound := by
  obtain ⟨decoder,dominated⟩ := deterministic_dominates mass reverse reverse_nonneg reverse_sum
  exact dominated.trans ((deterministic_capacity mass p q nonneg rows cols decoder).trans (all_decoders decoder))

theorem singleton {C : Type} (p : PMF C) (a : C) : eventProb p (· = a) = p a := PMF.toOuterMeasure_apply_singleton p a

omit [Nonempty A] [Fintype B] in
theorem bind_real (p : PMF A) (forward : A → PMF B) (b : B) :
    ((p.bind forward) b).toReal = ∑ a, (p a).toReal * (forward a b).toReal := by
  have h := event_bind_real p forward (· = b)
  simpa only [singleton] using h

def failure (p : PMF A) (forward : A → PMF B) (reverse : B → PMF A) : ℝ :=
  ∑ a, (p a).toReal * (eventProb ((forward a).bind reverse) (· ≠ a)).toReal

omit [Nonempty A] in
theorem different_probability (p : PMF A) (a : A) : (eventProb p (· ≠ a)).toReal = 1 - (p a).toReal := by
  classical
  rw [event_real_sum]
  calc
    _ = ∑ x, ((p x).toReal - if x = a then (p x).toReal else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = a <;> simp [h]
    _ = _ := by rw [Finset.sum_sub_distrib, sum_real_mass]; simp

omit [Nonempty A] in
theorem failure_eq_one_sub_success (p : PMF A) (forward : A → PMF B) (reverse : B → PMF A) :
    failure p forward reverse = 1 - ∑ a, ∑ b, ((p a).toReal * (forward a b).toReal) * (reverse b a).toReal := by
  unfold failure
  simp_rw [event_bind_real, different_probability, mul_sub, mul_one]
  simp only [Finset.sum_sub_distrib, sum_real_mass, mul_sub, mul_one, Finset.mul_sum]
  simp only [← mul_assoc]

theorem failure_lower (p : PMF A) (q : PMF B) (forward : A → PMF B) (reverse : B → PMF A)
    (preserve : p.bind forward = q) (bound : ℝ)
    (all_decoders : ∀ decoder, capacity (fun a => (p a).toReal) (fun b => (q b).toReal) decoder ≤ bound) :
    1 - bound ≤ failure p forward reverse := by
  have h := matrix_success_bound (fun a b => (p a).toReal * (forward a b).toReal)
    (fun a => (p a).toReal) (fun b => (q b).toReal) (fun b a => (reverse b a).toReal)
    (fun a b => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun a => by rw [← Finset.mul_sum, sum_real_mass, mul_one])
    (fun b => by rw [← bind_real, preserve])
    (fun b a => ENNReal.toReal_nonneg) (fun b => sum_real_mass (reverse b)) bound all_decoders
  rw [failure_eq_one_sub_success]
  linarith

omit [Nonempty A] in
theorem failure_identity_joint (p : PMF A) (forward : A → PMF A) :
    failure p forward (fun a => PMF.pure a) =
      (eventProb (p.bind fun a => (forward a).map fun b => (a,b)) (fun pair => pair.1 ≠ pair.2)).toReal := by
  rw [event_bind_real]
  simp only [failure, PMF.bind_pure, eventProb_map]
  simp only [ne_comm]

end
end Foundation.Probability.FiniteRecoveryError
