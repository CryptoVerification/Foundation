import Foundation.Crypto.Semantics.Probability.Facts
import Mathlib.Data.Nat.Prime.Basic

/-! Exact finite fair randomness. A seed has 2^n equiprobable values, including
unused bits. Every event therefore has an integer numerator over 2^n.
This is a realizability condition, not a runtime bound or an approximation. -/
namespace Foundation.Probability.FiniteFairSampling
open scoped ENNReal
noncomputable section

def Realizable {A : Type} (n : Nat) (law : PMF A) : Prop :=
  ∃ decode : Fin (2 ^ n) → A, (uniform (Fin (2 ^ n))).map decode = law

theorem event_count {A : Type} (n : Nat) (decode : Fin (2 ^ n) → A) (event : A → Prop) :
    ∃ k : Nat, eventProb ((uniform (Fin (2 ^ n))).map decode) event = (k : ℝ≥0∞) / (2 ^ n : Nat) := by
  classical
  refine ⟨Fintype.card {s : Fin (2 ^ n) // event (decode s)}, ?_⟩
  rw [eventProb_map]
  unfold eventProb uniform
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Fintype.card_fin]
  rfl

theorem event_real_count {A : Type} (n : Nat) (law : PMF A) (realizable : Realizable n law) (event : A → Prop) :
    ∃ k : Nat, (eventProb law event).toReal = (k : ℝ) / (2 ^ n : Nat) := by
  obtain ⟨decode,same⟩ := realizable
  obtain ⟨k,h⟩ := event_count n decode event
  rw [same] at h
  refine ⟨k,?_⟩
  rw [h, ENNReal.toReal_div]
  simp

theorem reciprocal_dvd {A : Type} (n d : Nat) (hd : 0 < d) (law : PMF A)
    (realizable : Realizable n law) (event : A → Prop)
    (probability : (eventProb law event).toReal = 1 / (d : ℝ)) : d ∣ 2 ^ n := by
  obtain ⟨k,hk⟩ := event_real_count n law realizable event
  have hN : (2 ^ n : Nat) ≠ 0 := by positivity
  have hNR : ((2 ^ n : Nat) : ℝ) ≠ 0 := by exact_mod_cast hN
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have equal : (d : ℝ) * k = ((2 ^ n : Nat) : ℝ) := by
    rw [probability] at hk
    have h := (div_eq_div_iff hdR hNR).mp hk
    nlinarith
  refine ⟨k,?_⟩
  exact_mod_cast equal.symm

theorem no_reciprocal_odd_factor {A : Type} (n d prime : Nat) (hd : 0 < d)
    (hp : Nat.Prime prime) (different : prime ≠ 2) (factor : prime ∣ d) (law : PMF A)
    (event : A → Prop) (probability : (eventProb law event).toReal = 1 / (d : ℝ)) :
    ¬Realizable n law := by
  intro realizable
  have divides := factor.trans (reciprocal_dvd n d hd law realizable event probability)
  exact different (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two divides)

theorem map {A B : Type} {n : Nat} {law : PMF A} (realizable : Realizable n law) (observe : A → B) :
    Realizable n (law.map observe) := by
  obtain ⟨decode,same⟩ := realizable
  refine ⟨observe ∘ decode,?_⟩
  rw [← PMF.map_comp, same]

theorem pure {A : Type} (n : Nat) (a : A) : Realizable n (PMF.pure a) := by
  refine ⟨fun _ => a, ?_⟩
  exact PMF.map_const _ _

theorem bit : Realizable 1 sampleBit := by
  refine ⟨finTwoEquiv, ?_⟩
  exact uniform_map_equiv finTwoEquiv

theorem bind {A B : Type} (n m : Nat) (law : PMF A) (kernel : A → PMF B)
    (first : Realizable n law) (second : ∀ a, Realizable m (kernel a)) :
    Realizable (n + m) (law.bind kernel) := by
  classical
  obtain ⟨draw,draw_law⟩ := first
  choose decode decode_law using second
  let e : Fin (2 ^ (n + m)) ≃ (Fin (2 ^ n) × Fin (2 ^ m)) :=
    Fintype.equivOfCardEq (by simp [pow_add])
  refine ⟨(fun s => decode (draw s.1) s.2) ∘ e, ?_⟩
  rw [← PMF.map_comp, uniform_map_equiv, ← uniform_pair, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (uniform (Fin (2 ^ n))).bind (fun i =>
    (uniform (Fin (2 ^ m))).map (decode (draw i))) = _
  simp_rw [decode_law]
  change (uniform (Fin (2 ^ n))).bind (kernel ∘ draw) = _
  rw [← PMF.bind_map, draw_law]

theorem reciprocal_error_lower {A : Type} (n d : Nat) (hd : 0 < d)
    (notDivides : ¬ d ∣ 2 ^ n) (law : PMF A) (realizable : Realizable n law) (event : A → Prop) :
    1 / ((d : ℝ) * (2 ^ n : Nat)) ≤ |(eventProb law event).toReal - 1 / (d : ℝ)| := by
  obtain ⟨k,hk⟩ := event_real_count n law realizable event
  have different : d * k ≠ 2 ^ n := by
    intro same
    exact notDivides ⟨k,same.symm⟩
  have gap : (1 : ℝ) ≤ |(d : ℝ) * k - (2 ^ n : Nat)| := by
    rcases lt_or_gt_of_ne different with smaller | larger
    · have h : (d : ℝ) * k + 1 ≤ (2 ^ n : Nat) := by exact_mod_cast Nat.succ_le_of_lt smaller
      rw [abs_of_nonpos (by linarith : (d : ℝ) * k - (2 ^ n : Nat) ≤ 0)]
      linarith
    · have h : ((2 ^ n : Nat) : ℝ) + 1 ≤ (d : ℝ) * k := by exact_mod_cast Nat.succ_le_of_lt larger
      rw [abs_of_nonneg (by linarith : 0 ≤ (d : ℝ) * k - (2 ^ n : Nat))]
      linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : (0 : ℝ) < (2 ^ n : Nat) := by positivity
  have fraction : (k : ℝ) / (2 ^ n : Nat) - 1 / (d : ℝ) =
      ((d : ℝ) * k - (2 ^ n : Nat)) / ((d : ℝ) * (2 ^ n : Nat)) := by
    field_simp
  rw [hk, fraction, abs_div, abs_of_pos (mul_pos hdR hN)]
  exact (div_le_div_iff_of_pos_right (mul_pos hdR hN)).mpr gap

end
end Foundation.Probability.FiniteFairSampling
