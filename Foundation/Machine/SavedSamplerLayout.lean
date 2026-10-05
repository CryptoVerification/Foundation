import Foundation.Machine.SavedRejectionSamplingSemantics

namespace Machine.RejectionSampling.Saved

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

/-- Every halted branch inspected after any number of actual retry blocks
has an accepted sample and the physical tape layout required by the native
padding continuation. No arbitrary successful branch is selected. -/
theorem trials_halted_layout (before : List (Option Bool))
    (modulus previous : List Bool) (trials : Nat)
    (hPrevious : previous.length ≤ modulus.length)
    (finish : Configuration)
    (hMember : finish ∈ (evalConfigWithin program (trialStart before modulus previous)
      (trials*(10*modulus.length+7))).support) (hHalt : finish.halted = true) :
    ∃ sample : List Bool, sample.length = modulus.length ∧
      Binary.value sample < Binary.value modulus ∧
      finish.inputTape.Equivalent {left := modulus.reverse.map some ++ none::before} ∧
      finish.outputTape.Equivalent {left := sample.reverse.map some} ∧
      finish.outputBits = sample := by
  induction trials generalizing previous finish with
  | zero =>
    simp [evalConfigWithin] at hMember
    subst finish
    simp [trialStart] at hHalt
  | succ trials ih =>
    have budget : (trials+1)*(10*modulus.length+7) =
        (10*modulus.length+7)+trials*(10*modulus.length+7) := by simp [Nat.add_mul, Nat.add_comm]
    rw [budget, evalConfigWithin_add, eval_trial before modulus previous hPrevious] at hMember
    obtain ⟨middle, hMiddle, hTail⟩ := (PMF.mem_support_bind_iff ..).mp hMember
    obtain ⟨draw, _, hDraw⟩ := (PMF.mem_support_map_iff ..).mp hMiddle
    subst middle
    by_cases hAccepted : Binary.value (List.ofFn draw) < Binary.value modulus
    · have hStopped : (trialResult before modulus draw).halted = true := by
        rw [trialResult_halted, if_pos hAccepted]
      rw [eval_halted _ _ hStopped] at hTail
      have same : finish = trialResult before modulus draw := by simpa using hTail
      subst finish
      refine ⟨List.ofFn draw, by simp, hAccepted, ?_, ?_, ?_⟩
      · rw [trialResult_accepted_input before modulus draw hAccepted]
        exact Tape.Equivalent.refl _
      · rw [trialResult_accepted_output before modulus draw hAccepted]
        exact Tape.Equivalent.refl _
      · exact trialResult_output before modulus draw
    · have tailTrace := (mem_support_evalConfigWithin_iff _ _ _ _).mp hTail
      obtain ⟨canonical, canonicalTrace, same⟩ := tailTrace.exists_equivalent
        (trialResult_retry_equivalent before modulus draw hAccepted)
      have canonicalHalt : canonical.halted = true := same.2.1.symm.trans hHalt
      obtain ⟨sample, hLength, hValue, hInput, hOutput, hBits⟩ :=
        ih (List.ofFn draw) (by simp) canonical
          ((mem_support_evalConfigWithin_iff _ _ _ _).mpr canonicalTrace) canonicalHalt
      exact ⟨sample, hLength, hValue, same.2.2.1.trans hInput,
        same.2.2.2.trans hOutput, same.outputBits.trans hBits⟩

/-- The sampler entry's native validation and head rewind preserve the
same accepted-branch layout. This includes every successful retry count. -/
theorem prepared_halted_layout (before : List (Option Bool))
    (leading : List Bool) (hLeading : leading ≠ []) (trials : Nat)
    (finish : Configuration)
    (hMember : finish ∈ (evalConfigWithin program (initial before (leading++[true]))
      (preparationSteps (leading++[true])+trials*(10*(leading++[true]).length+7))).support)
    (hHalt : finish.halted = true) :
    ∃ sample : List Bool, sample.length = (leading++[true]).length ∧
      Binary.value sample < Binary.value (leading++[true]) ∧
      finish.inputTape.Equivalent {left := (leading++[true]).reverse.map some ++ none::before} ∧
      finish.outputTape.Equivalent {left := sample.reverse.map some} ∧
      finish.outputBits = sample := by
  rw [evalConfigWithin_add, eval_prepare before leading hLeading, PMF.pure_bind] at hMember
  have trace := (mem_support_evalConfigWithin_iff _ _ _ _).mp hMember
  obtain ⟨canonical, canonicalTrace, same⟩ := trace.exists_equivalent
    (validatedTrialStart_equivalent before (leading++[true]))
  obtain ⟨sample, hLength, hValue, hInput, hOutput, hBits⟩ :=
    trials_halted_layout before (leading++[true]) [] trials (by simp) canonical
      ((mem_support_evalConfigWithin_iff _ _ _ _).mpr canonicalTrace)
      (same.2.1.symm.trans hHalt)
  exact ⟨sample, hLength, hValue, same.2.2.1.trans hInput,
    same.2.2.2.trans hOutput, same.outputBits.trans hBits⟩

end Machine.RejectionSampling.Saved
