import Foundation.Crypto.Semantics.Probability.Facts
import Mathlib.Algebra.BigOperators.Fin

/-! A computable finite-interval decoder for integer-weight distributions.
The probability law is semantic: no machine runtime claim is made here. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal

def countSampleEquiv {m D : ℕ} (w : Fin m → ℕ) (hw : ∑ i, w i = D) :
    Fin D ≃ (i : Fin m) × Fin (w i) :=
  (finCongr hw).symm.trans finSigmaFinEquiv.symm

def sampleCounts {m D : ℕ} (w : Fin m → ℕ) (hw : ∑ i, w i = D)
    (draw : Fin D) : Fin m := (countSampleEquiv w hw draw).1

theorem sampleCounts_fiber_card {m D : ℕ} (w : Fin m → ℕ)
    (hw : ∑ i, w i = D) (i : Fin m) :
    Fintype.card {draw : Fin D // sampleCounts w hw draw = i} = w i := by
  classical
  let e : {draw : Fin D // sampleCounts w hw draw = i} ≃ Fin (w i) :=
    (Equiv.subtypeEquivOfSubtype (p := fun s : (j : Fin m) × Fin (w j) => s.1 = i)
      (countSampleEquiv w hw)).trans (Equiv.sigmaSubtype i)
  simpa using Fintype.card_congr e

theorem sampleCounts_event_probability {m D : ℕ} [NeZero D]
    (w : Fin m → ℕ) (hw : ∑ i, w i = D) (i : Fin m) :
    Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin D))
      (fun draw => sampleCounts w hw draw = i) = (w i : ℝ≥0∞) / D := by
  classical
  unfold Foundation.Probability.eventProb Foundation.Probability.uniform
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Fintype.card_fin]
  have hc : Fintype.card ↑{a : Fin D | sampleCounts w hw a = i} = w i := by
    calc
      _ = Fintype.card {draw : Fin D // sampleCounts w hw draw = i} :=
        Fintype.card_congr (Equiv.refl _)
      _ = w i := sampleCounts_fiber_card w hw i
  rw [hc]

def bitIndexEquiv (r : ℕ) : (Fin r → Bool) ≃ Fin (2 ^ r) :=
  (Equiv.piCongrRight (fun _ : Fin r => finTwoEquiv.symm)).trans
    (finPiFinEquiv.trans (finCongr (by simp)))

/-- Independent uniform bits realize the exact integer-weight law. -/
theorem sampleCounts_bits_event_probability {m : ℕ} (r : ℕ)
    (w : Fin m → ℕ) (hw : ∑ i, w i = 2 ^ r) (i : Fin m) :
    Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin r → Bool))
      (fun bits => sampleCounts w hw (bitIndexEquiv r bits) = i) =
        (w i : ℝ≥0∞) / (2 ^ r : ℕ) := by
  rw [← Foundation.Probability.eventProb_map
    (Foundation.Probability.uniform (Fin r → Bool)) (bitIndexEquiv r)
    (fun draw => sampleCounts w hw draw = i)]
  rw [Foundation.Probability.uniform_map_equiv]
  exact sampleCounts_event_probability w hw i

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
