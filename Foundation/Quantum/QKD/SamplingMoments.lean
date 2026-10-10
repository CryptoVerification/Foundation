import Foundation.Quantum.QKD.SamplingInclusion
import Foundation.Quantum.Mixture

/-! Exact first and second moments of errors in a uniform fixed-size test.
The negative dependence is derived from inclusion probabilities, never
replaced by independent sampling. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

def fullSample (n k : Nat) (hk : k ≤ n) : PMF (Finset (Fin n)) :=
  sample Finset.univ k (by simpa using hk)

def expectation {X : Type} [Fintype X] (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

theorem expectation_const {X : Type} [Fintype X] (p : PMF X) (r : ℝ) :
    expectation p (fun _ => r) = r := by
  unfold expectation
  rw [← Finset.sum_mul, Density.probability_weights, one_mul]

theorem expectation_add {X : Type} [Fintype X] (p : PMF X) (f g : X → ℝ) :
    expectation p (fun x => f x + g x) = expectation p f + expectation p g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub {X : Type} [Fintype X] (p : PMF X) (f g : X → ℝ) :
    expectation p (fun x => f x - g x) = expectation p f - expectation p g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const {X : Type} [Fintype X] (p : PMF X) (f : X → ℝ) (r : ℝ) :
    expectation p (fun x => f x * r) = expectation p f * r := by
  simp only [expectation, mul_assoc, Finset.sum_mul]

theorem expectation_sum {X Y : Type} [Fintype X] (p : PMF X) (s : Finset Y) (f : Y → X → ℝ) :
    expectation p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

def indicator {n : Nat} (T : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ T then 1 else 0

def hits {n : Nat} (E T : Finset (Fin n)) : ℝ := ∑ i ∈ E, indicator T i

theorem hits_card {n : Nat} (E T : Finset (Fin n)) : hits E T = (E ∩ T).card := by
  simp only [hits, indicator, Finset.sum_boole, Finset.filter_mem_eq_inter]

theorem indicator_mean {n : Nat} (k : Nat) (hk : k ≤ n) (i : Fin n) :
    expectation (fullSample n k hk) (fun T => indicator T i) = (k : ℝ)/n := by
  have h : (Foundation.Probability.eventProb (fullSample n k hk) (fun T => i ∈ T)).toReal =
      (k : ℝ)/(Finset.univ : Finset (Fin n)).card :=
    singleton_probability_real Finset.univ k (by simpa using hk) i (Finset.mem_univ _)
  rw [eventProb_toReal] at h
  simpa only [expectation, indicator, mul_ite, mul_one, mul_zero, Finset.card_univ, Fintype.card_fin] using h

theorem indicator_product_mean {n : Nat} (k : Nat) (hk : k ≤ n) (i j : Fin n) :
    expectation (fullSample n k hk) (fun T => indicator T i * indicator T j) =
      if i = j then (k : ℝ)/n else (k : ℝ)*(k-1)/((n : ℝ)*(n-1)) := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have he : (fun T : Finset (Fin n) => indicator T i * indicator T i) = (fun T => indicator T i) := by
      funext T
      unfold indicator
      split_ifs <;> norm_num
    rw [he]
    exact indicator_mean k hk i
  · rw [if_neg hij]
    have h : (Foundation.Probability.eventProb (fullSample n k hk) (fun T => i ∈ T ∧ j ∈ T)).toReal =
        (k : ℝ)*(k-1)/(((Finset.univ : Finset (Fin n)).card : ℝ)*((Finset.univ : Finset (Fin n)).card-1)) :=
      pair_probability_real Finset.univ k (by simpa using hk) i j (Finset.mem_univ _) (Finset.mem_univ _) hij
    rw [eventProb_toReal] at h
    have he : (fun T : Finset (Fin n) => indicator T i * indicator T j) =
        (fun T => if i ∈ T ∧ j ∈ T then 1 else 0) := by
      funext T
      unfold indicator
      split_ifs <;> simp_all
    rw [he]
    simpa only [expectation, mul_ite, mul_one, mul_zero, Finset.card_univ, Fintype.card_fin] using h

theorem hits_mean {n : Nat} (k : Nat) (hk : k ≤ n) (E : Finset (Fin n)) :
    expectation (fullSample n k hk) (hits E) = (k : ℝ)/n * E.card := by
  unfold hits
  rw [expectation_sum]
  simp only [indicator_mean, Finset.sum_const, nsmul_eq_mul]
  ring

theorem hits_second_moment {n : Nat} (k : Nat) (hk : k ≤ n) (E : Finset (Fin n)) :
    expectation (fullSample n k hk) (fun T => hits E T ^ 2) =
      (k : ℝ)/n * E.card + ((k : ℝ)*(k-1)/((n : ℝ)*(n-1))) * ((E.card : ℝ)^2-E.card) := by
  classical
  simp only [hits, pow_two, Finset.sum_mul_sum]
  rw [expectation_sum]
  simp_rw [expectation_sum, indicator_product_mean]
  let a : ℝ := k / n
  let b : ℝ := (k : ℝ)*(k-1)/((n : ℝ)*(n-1))
  have hrow (i : Fin n) (hi : i ∈ E) :
      (∑ j ∈ E, if i = j then a else b) = (E.card : ℝ)*b + a-b := by
    have he (j : Fin n) : (if i = j then a else b) = b + (if j = i then a-b else 0) := by
      by_cases h : i = j <;> simp [h, eq_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hi]
    ring
  change (∑ i ∈ E, ∑ j ∈ E, if i = j then a else b) = a*E.card+b*((E.card : ℝ)*(E.card : ℝ)-E.card)
  rw [Finset.sum_congr rfl (fun i hi => hrow i hi)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end
end Foundation.Quantum.QKD.Sampling
