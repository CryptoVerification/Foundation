import Foundation.Machine.RejectionContinuationSemantics

namespace Machine.RejectionContinuation

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

private theorem partial_sum (encode : List Bool → List Bool) (modulus output : List Bool) (trials : Nat) :
    (∑' sample : List Bool, if output = encode sample then
      RejectionSampling.trialWeights modulus trials (some sample) else 0) =
    ((RejectionSampling.trialWeights modulus trials).map
      (Option.map (encode))) (some output) := by
  classical
  let f : Option (List Bool) → ℝ≥0∞ := fun value =>
    if some output = Option.map (encode) value then
      RejectionSampling.trialWeights modulus trials value else 0
  have h := (Equiv.optionEquivSumPUnit.{0,0} (List Bool)).symm.tsum_eq f
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at h
  simpa [f, PMF.map_apply, eq_comm] using h

/-- The native sampler, its physical width restoration, and its actual
caller halt together realize the exact uniform fixed-width residue law.
This compares unrenormalized eventual output probabilities of the linked
code; no mathematical post-decoder replaces the padding instructions. -/
theorem outputMass_uniform (tail : Program) (encode : List Bool → List Bool) (charge : Nat) (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (complete : Completion tail encode charge before width leading)
    [Nonempty (Fin (Binary.value (leading++[true])))] (output : List Bool) :
    outputMassFrom (program tail)
      (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true])) output =
    ((uniform (Fin (Binary.value (leading++[true])))).map
      (fun a => encode (Binary.encode (leading++[true]).length a.val))) output := by
  classical
  let bits := leading++[true]
  let sourceLaw := (uniform (Fin (Binary.value bits))).map (fun a => Binary.encode bits.length a.val)
  let pad := fun sample : List Bool => encode sample
  have sourceMass (sample : List Bool) : Machine.outputMass RejectionSampling.program bits sample =
      sourceLaw sample := congrArg (fun law : PMF (List Bool) => law sample)
        (RejectionSampling.evalLimit_canonical leading hLeading)
  have sourceSup (sample : List Bool) : sourceLaw sample =
      ⨆ trials : Nat, RejectionSampling.trialWeights bits trials (some sample) := by
    rw [← sourceMass sample, RejectionSampling.outputMass_geometric leading hLeading sample]
    simp_rw [RejectionSampling.trialWeights_some]
    rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]
  have dominates (out : List Bool) : (sourceLaw.map pad) out ≤
      outputMassFrom (program tail) (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) bits) out := by
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
        rw [show pad = (encode) from rfl,
          partial_sum encode bits out trials]
        apply (accepted_output_after_trials_le tail encode charge before width leading hLeading hWidth complete trials out).trans
        unfold outputMassFrom
        exact le_iSup (fun steps => ((evalConfigWithin (program tail)
          (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) bits) steps).map
            (fun c => if c.halted then some c.outputBits else none)) (some out)) _
  have exactLaw := outputMassFrom_eq_of_dominates (program tail)
    (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) bits) (sourceLaw.map pad) dominates
  simpa only [sourceLaw, PMF.map_comp, Function.comp_def] using exactLaw output

end Machine.RejectionContinuation
