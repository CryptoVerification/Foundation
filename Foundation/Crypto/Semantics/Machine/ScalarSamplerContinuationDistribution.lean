import Foundation.Crypto.Semantics.Machine.ScalarSamplerContinuationSemantics

namespace Machine.ScalarSamplerContinuation

open Foundation.Probability
open scoped ENNReal

private theorem tsum_iSup_of_monotone {α : Type*} (f : Nat → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

private theorem weights_some_monotone (modulus sample : List Bool) :
    Monotone (fun trials => RejectionSampling.trialWeights modulus trials (some sample)) := by
  intro i j hij
  dsimp only
  rw [RejectionSampling.trialWeights_some, RejectionSampling.trialWeights_some]
  apply mul_le_mul_of_nonneg_left _ (bot_le)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (fun _ _ _ => bot_le)

private theorem partial_sum (width : Nat) (modulus output : List Bool) (trials : Nat) :
    (∑' sample : List Bool, if output = Binary.encode width (Binary.value sample) then
      RejectionSampling.trialWeights modulus trials (some sample) else 0) =
    ((RejectionSampling.trialWeights modulus trials).map
      (Option.map (fun sample => Binary.encode width (Binary.value sample)))) (some output) := by
  classical
  let f : Option (List Bool) → ℝ≥0∞ := fun value =>
    if some output = Option.map (fun sample => Binary.encode width (Binary.value sample)) value then
      RejectionSampling.trialWeights modulus trials value else 0
  have h := (Equiv.optionEquivSumPUnit.{0,0} (List Bool)).symm.tsum_eq f
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at h
  simpa [f, PMF.map_apply, eq_comm] using h

/-- The native sampler, its physical width restoration, and its actual
caller halt together realize the exact uniform fixed-width residue law.
This compares unrenormalized eventual output probabilities of the linked
code; no mathematical post-decoder replaces the padding instructions. -/
theorem outputMass_uniform (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    [Nonempty (Fin (Binary.value (leading++[true])))] (output : List Bool) :
    outputMassFrom program
      (RejectionSampling.Saved.initial (List.replicate width (some true)) (leading++[true])) output =
    ((uniform (Fin (Binary.value (leading++[true])))).map
      (fun a => Binary.encode width a.val)) output := by
  classical
  let bits := leading++[true]
  let sourceLaw := (uniform (Fin (Binary.value bits))).map (fun a => Binary.encode bits.length a.val)
  let pad := fun sample : List Bool => Binary.encode width (Binary.value sample)
  have sourceMass (sample : List Bool) : Machine.outputMass RejectionSampling.program bits sample =
      sourceLaw sample := congrArg (fun law : PMF (List Bool) => law sample)
        (RejectionSampling.evalLimit_canonical leading hLeading)
  have sourceSup (sample : List Bool) : sourceLaw sample =
      ⨆ trials : Nat, RejectionSampling.trialWeights bits trials (some sample) := by
    rw [← sourceMass sample, RejectionSampling.outputMass_geometric leading hLeading sample]
    simp_rw [RejectionSampling.trialWeights_some]
    rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]
  have dominates (out : List Bool) : (sourceLaw.map pad) out ≤
      outputMassFrom program (RejectionSampling.Saved.initial (List.replicate width (some true)) bits) out := by
    rw [PMF.map_apply]
    calc
      _ = ∑' sample : List Bool, ⨆ trials : Nat,
          if out = pad sample then RejectionSampling.trialWeights bits trials (some sample) else 0 := by
        apply tsum_congr
        intro sample
        by_cases hit : out = pad sample
        · simp only [hit, ite_true, sourceSup]
        · simp [hit]
      _ = ⨆ trials : Nat, ∑' sample : List Bool,
          if out = pad sample then RejectionSampling.trialWeights bits trials (some sample) else 0 := by
        apply tsum_iSup_of_monotone
        intro sample i j hij
        split_ifs
        · exact weights_some_monotone bits sample hij
        · exact le_rfl
      _ ≤ _ := by
        apply iSup_le
        intro trials
        rw [show pad = (fun sample => Binary.encode width (Binary.value sample)) from rfl,
          partial_sum width bits out trials]
        apply (accepted_output_after_trials_le width leading hLeading hWidth trials out).trans
        unfold outputMassFrom
        exact le_iSup (fun steps => ((evalConfigWithin program
          (RejectionSampling.Saved.initial (List.replicate width (some true)) bits) steps).map
            (fun c => if c.halted then some c.outputBits else none)) (some out)) _
  have exactLaw := outputMassFrom_eq_of_dominates program
    (RejectionSampling.Saved.initial (List.replicate width (some true)) bits) (sourceLaw.map pad) dominates
  have mappedLaw : sourceLaw.map pad = (uniform (Fin (Binary.value bits))).map
      (fun a => Binary.encode width a.val) := by
    dsimp only [sourceLaw]
    rw [PMF.map_comp]
    congr 1
    funext a
    exact congrArg (Binary.encode width) (Binary.value_encode (a.isLt.trans (Binary.value_lt bits)))
  rw [← mappedLaw]
  exact exactLaw output

/-- Natural-number modulus form, suitable for the public scalar domain of
a prime-order group. The modulus is canonicalized before drawing bits. -/
theorem outputMass_nat (width q : Nat) [NeZero q] (hTwo : 2 ≤ q) (hFit : q < 2^width)
    (output : List Bool) :
    outputMassFrom program
      (RejectionSampling.Saved.initial (List.replicate width (some true)) q.bits) output =
      ((uniform (Fin q)).map (fun a => Binary.encode width a.val)) output := by
  obtain ⟨leading, hCanonical⟩ := Binary.nat_bits_canonical q (by omega)
  have hValue : Binary.value (leading++[true]) = q := by rw [← hCanonical, Binary.value_nat_bits]
  have hLeading : leading ≠ [] := by
    intro empty
    rw [empty] at hValue
    norm_num [Binary.value] at hValue
    omega
  have hLength : q.bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  let : Nonempty (Fin (Binary.value (leading++[true]))) := ⟨⟨0, by rw [hValue]; omega⟩⟩
  have law := outputMass_uniform width leading hLeading (hCanonical ▸ hLength) output
  subst q
  simpa only [hCanonical] using law

/-- The same natural-number invocation has a linear expected transition
bound in its retained public width, independent of the width/modulus ratio. -/
theorem expectedSteps_nat (width q : Nat) (hTwo : 2 ≤ q) (hFit : q < 2^width) :
    expectedStepsFrom program
      (RejectionSampling.Saved.initial (List.replicate width (some true)) q.bits) ≤
        (50*(width+1) : Nat) := by
  obtain ⟨leading, hCanonical⟩ := Binary.nat_bits_canonical q (by omega)
  have hValue : Binary.value (leading++[true]) = q := by rw [← hCanonical, Binary.value_nat_bits]
  have hLeading : leading ≠ [] := by
    intro empty
    rw [empty] at hValue
    norm_num [Binary.value] at hValue
    omega
  have hLength : q.bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  simpa only [← hCanonical] using expectedSteps_le width leading hLeading (hCanonical ▸ hLength)

end Machine.ScalarSamplerContinuation
