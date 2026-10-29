import Foundation.Crypto.Semantics.Probability.FiniteObserverVariation
import Mathlib.Data.Fintype.Card

/-! A single finite uniform draw couples two integer-count Boolean laws.
The mismatch event is the interval between their thresholds. These semantic
coupling certificates do not prescribe or compile a native sampler. -/
namespace Foundation.Probability.FiniteBooleanThreshold
open scoped BigOperators ENNReal

noncomputable def law (count : ℕ) : PMF Bool :=
  (uniform (Fin 256)).map (fun draw => decide (draw.val < count))

def bit (count : ℕ) (draw : Fin 256) : Bool := decide (draw.val < count)

theorem initial_card (count : ℕ) (h : count ≤ 256) :
    Fintype.card {draw : Fin 256 // draw.val < count} = count := by
  let e : {draw : Fin 256 // draw.val < count} ≃ Fin count :=
    {toFun := fun x => ⟨x.val.val, x.property⟩
     invFun := fun x => ⟨⟨x.val, lt_of_lt_of_le x.isLt h⟩, x.isLt⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  simpa only [Fintype.card_fin] using Fintype.card_congr e

theorem true_probability (count : ℕ) (h : count ≤ 256) :
    eventProb (law count) (· = true) = (count : ℝ≥0∞) / 256 := by
  rw [law, eventProb_map]
  have he : (fun draw : Fin 256 => decide (draw.val < count) = true) =
      (fun draw => draw.val < count) := by
    funext draw
    simp
  rw [he]
  unfold eventProb uniform
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Fintype.card_fin]
  have hc : Fintype.card ↑{draw : Fin 256 | draw.val < count} = count := by
    calc
      _ = Fintype.card {draw : Fin 256 // draw.val < count} := Fintype.card_congr (Equiv.refl _)
      _ = count := initial_card count h
  rw [hc]
  norm_num

theorem bool_ext_true_real (p q : PMF Bool)
    (h : (eventProb p (· = true)).toReal = (eventProb q (· = true)).toReal) : p = q := by
  change (p.toOuterMeasure {true}).toReal = (q.toOuterMeasure {true}).toReal at h
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at h
  have hp := sum_real_mass p
  have hq := sum_real_mass q
  simp only [Fintype.sum_bool] at hp hq
  apply PMF.ext
  intro b
  have hr : (p b).toReal = (q b).toReal := by cases b <;> linarith
  calc
    p b = ENNReal.ofReal (p b).toReal := (ENNReal.ofReal_toReal (p.apply_ne_top b)).symm
    _ = ENNReal.ofReal (q b).toReal := congrArg ENNReal.ofReal hr
    _ = q b := ENNReal.ofReal_toReal (q.apply_ne_top b)

theorem interval_card (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 256) :
    Fintype.card {draw : Fin 256 // a ≤ draw.val ∧ draw.val < b} = b - a := by
  let e : {draw : Fin 256 // a ≤ draw.val ∧ draw.val < b} ≃ Fin (b - a) :=
    {toFun := fun x => ⟨x.val.val - a, by have := x.property; omega⟩
     invFun := fun x => ⟨⟨x.val + a, by omega⟩, by
       change a ≤ x.val + a ∧ x.val + a < b
       constructor <;> omega⟩
     left_inv := by intro x; apply Subtype.ext; apply Fin.ext; exact Nat.sub_add_cancel x.property.1
     right_inv := by intro x; apply Fin.ext; exact Nat.add_sub_cancel _ _}
  simpa only [Fintype.card_fin] using Fintype.card_congr e

theorem interval_probability (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 256) :
    eventProb (uniform (Fin 256)) (fun draw => a ≤ draw.val ∧ draw.val < b) =
      ((b - a : ℕ) : ℝ≥0∞) / 256 := by
  unfold eventProb uniform
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Fintype.card_fin]
  have hc : Fintype.card ↑{draw : Fin 256 | a ≤ draw.val ∧ draw.val < b} = b - a := by
    calc
      _ = Fintype.card {draw : Fin 256 // a ≤ draw.val ∧ draw.val < b} := Fintype.card_congr (Equiv.refl _)
      _ = b - a := interval_card a b hab hb
  rw [hc]
  norm_num

def bad (a b : ℕ) (draw : Fin 256) : Prop := bit a draw ≠ bit b draw

theorem bad_ordered (a b : ℕ) (hab : a ≤ b) :
    bad a b = (fun draw : Fin 256 => a ≤ draw.val ∧ draw.val < b) := by
  funext draw
  apply propext
  by_cases ha : draw.val < a <;> by_cases hb : draw.val < b <;>
    simp [bad, bit, ha, hb] <;> omega

theorem bad_ordered_real (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 256) :
    (eventProb (uniform (Fin 256)) (bad a b)).toReal = |(a : ℝ) / 256 - (b : ℝ) / 256| := by
  rw [bad_ordered a b hab, interval_probability a b hab hb]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_sub hab]
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  rw [abs_of_nonpos (by linarith : (a : ℝ) / 256 - (b : ℝ) / 256 ≤ 0)]
  ring

theorem bad_real (a b : ℕ) (ha : a ≤ 256) (hb : b ≤ 256) :
    (eventProb (uniform (Fin 256)) (bad a b)).toReal = |(a : ℝ) / 256 - (b : ℝ) / 256| := by
  rcases le_total a b with hab | hba
  · exact bad_ordered_real a b hab hb
  · have he : bad a b = bad b a := by funext draw; exact propext ne_comm
    rw [he, bad_ordered_real b a hba ha, abs_sub_comm]

theorem bad_eq_gap (a b : ℕ) (ha : a ≤ 256) (hb : b ≤ 256) :
    eventProb (uniform (Fin 256)) (bad a b) =
      probabilityGap (eventProb (law a) (· = true)) (eventProb (law b) (· = true)) := by
  rw [probabilityGap_eq_ofReal_abs _ _
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp))),
    true_probability a ha, true_probability b hb]
  have hn : eventProb (uniform (Fin 256)) (bad a b) ≠ ∞ :=
    ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp))
  rw [← ENNReal.ofReal_toReal hn, bad_real a b ha hb]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]

end Foundation.Probability.FiniteBooleanThreshold
