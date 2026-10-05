import Foundation.Crypto.Semantics.Machine.SavedScalarSamplerContinuation
import Foundation.Crypto.Semantics.Machine.ConfigurationExpectation

namespace Machine.ScalarSamplerContinuation.Saved

open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private def sampleSteps (leading : List Bool) (trials : Nat) : Nat :=
  RejectionSampling.preparationSteps (leading++[true]) + trials*(10*(leading++[true]).length+7)

private def start (before : List (Option Bool)) (width : Nat) (bits : List Bool) : Configuration :=
  RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) bits

private def returned (c : Configuration) : Configuration :=
  if c.halted then c.resumeAt entry else c.rebasePc 0

private theorem invocation (before : List (Option Bool)) (width : Nat) (bits : List Bool) (steps : Nat) :
    evalReturnWithin program entry (start before width bits) steps =
      (evalConfigWithin RejectionSampling.program (start before width bits) steps).map returned := by
  have layout : program = Program.withSubroutine [] RejectionSampling.program
      (ScalarSamplePadding.program.asSubroutine entry exit ++ [.halt]) entry := by
    simp [program, Program.followedBy, Program.withSubroutine, entry, exit]
  rw [layout]
  have law := RejectionSampling.Saved.eval_invocation []
    (ScalarSamplePadding.program.asSubroutine entry exit ++ [.halt]) entry
    (by intro pc hpc; simp only [List.length_nil, zero_add]; unfold entry; omega)
    (List.replicate width (some true) ++ none::before) bits steps
  have rebaseZero (c : Configuration) : c.rebasePc 0 = c := by cases c; simp [Configuration.rebasePc]
  change _ = (evalConfigWithin RejectionSampling.program (start before width bits) steps).map
    (fun d => if d.halted then d.resumeAt entry else d.rebasePc 0)
  simpa only [List.length_nil, rebaseZero, start] using law

private theorem accepted_continuation (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (trials : Nat) (accepted : Configuration)
    (member : accepted ∈ (evalConfigWithin RejectionSampling.program
      (start before width (leading++[true])) (sampleSteps leading trials)).support)
    (halted : accepted.halted = true) :
    ∃ finish : Configuration, finish.halted = true ∧
      finish.outputBits = Binary.encode width (Binary.value accepted.outputBits) ∧
      ∀ extra, evalConfigWithin program (accepted.resumeAt entry) (13*width+18+extra) =
        PMF.pure finish := by
  obtain ⟨sample, hLength, _, hInput, hOutput, hBits⟩ :=
    RejectionSampling.Saved.prepared_halted_layout (List.replicate width (some true) ++ none::before) leading
      hLeading trials accepted member halted
  obtain ⟨finish, hHalt, hCode, hEval⟩ := continuation_eval_saved before width (leading++[true]) sample
    hWidth (hLength.le.trans hWidth) accepted hInput hOutput
  exact ⟨finish, hHalt, hBits.symm ▸ hCode, hEval⟩

/-- Whole native evaluation after the retry inspection budget and the
charged fixed-width continuation budget. Returned branches execute the
continuation; unreturned branches retain their actual running configurations. -/
theorem eval_after_trials (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width) (trials : Nat) :
    (evalConfigWithin program (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before)
      (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7) + (13*width+18))).map
        (fun c => if c.halted then some c.outputBits else none) =
      (evalConfigWithin RejectionSampling.program
        (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true]))
        (RejectionSampling.preparationSteps (leading++[true]) +
          trials*(10*(leading++[true]).length+7))).bind
        (fun c => (evalConfigWithin program
          (if c.halted then c.resumeAt entry else c.rebasePc 0) (13*width+18)).map
            (fun d => if d.halted then some d.outputBits else none)) := by
  change (evalConfigWithin program (start before width (leading++[true]))
    (sampleSteps leading trials+(13*width+18))).map report = _
  have stable : ∀ d ∈ (evalReturnWithin program entry (start before width (leading++[true]))
      (sampleSteps leading trials)).support,
      d.pc = entry → ∀ extra,
        (evalConfigWithin program d (13*width+18+extra)).map report =
          (evalConfigWithin program d (13*width+18)).map report := by
    intro d member hPc extra
    rw [invocation before] at member
    obtain ⟨c, hc, hSame⟩ := (PMF.mem_support_map_iff ..).mp member
    subst d
    cases hHalt : c.halted with
    | false =>
      have trace := (mem_support_evalConfigWithin_iff _ _ _ _).mp hc
      have run := trace.toRunsFor_of_running hHalt
      have inside := (run.toRunsInside_of_closed (by change 0 < 50; decide)
        RejectionSampling.control_closed hHalt).2
      have impossible : c.pc = entry := by simpa [returned, hHalt, Configuration.rebasePc] using hPc
      unfold entry at impossible
      omega
    | true =>
      obtain ⟨finish, _, _, hEval⟩ := accepted_continuation before width leading hLeading hWidth trials c hc hHalt
      simpa only [returned, hHalt, ↓reduceIte, Nat.add_zero] using
        congrArg (fun law : PMF Configuration => law.map report) ((hEval extra).trans (hEval 0).symm)
  rw [evalConfigWithin_after_return program entry _ (sampleSteps leading trials)
    (13*width+18) report stable, invocation before, PMF.bind_map]
  rfl

/-- Padding and the actual caller halt add bounded work without increasing
the retry timeout probability. This is a statement about the linked native
program, including branches which reject arbitrarily many times. -/
theorem timeout_after_trials_le (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width) (trials : Nat) :
    ((evalConfigWithin program (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before)
      (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7) + (13*width+18))).map
        (fun c => if c.halted then some c.outputBits else none)) none ≤ (2⁻¹ : ℝ≥0∞)^trials := by
  classical
  rw [eval_after_trials before width leading hLeading hWidth trials]
  let law := evalConfigWithin RejectionSampling.program (start before width (leading++[true]))
    (sampleSteps leading trials)
  have hTimeout : ((law.map report) none) ≤ (2⁻¹ : ℝ≥0∞)^trials :=
    RejectionSampling.Saved.timeout_prepared_trials_le_half
      (List.replicate width (some true) ++ none::before) leading hLeading trials
  apply le_trans _ hTimeout
  rw [PMF.bind_apply, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  change law c * _ ≤ _
  by_cases hZero : law c = 0
  · simp only [hZero, zero_mul, ite_self, le_refl]
  · have member : c ∈ law.support := (PMF.mem_support_iff ..).mpr hZero
    cases hHalt : c.halted with
    | false =>
      simp only [report, hHalt, Bool.false_eq_true, ↓reduceIte, ite_true]
      exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    | true =>
      obtain ⟨finish, hStopped, _, hEval⟩ := accepted_continuation before width leading hLeading hWidth
        trials c member hHalt
      simp only [hHalt, ↓reduceIte]
      rw [show 13*width+18 = 13*width+18+0 by omega, hEval 0, PMF.pure_map]
      simp [report, hHalt, hStopped, PMF.pure_apply]

/-- Each finite accepted part of the exact retry law appears, with its
full probability, in the native fixed-width output law after the charged
continuation. Timeout branches are retained rather than renormalized. -/
theorem accepted_output_after_trials_le (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (trials : Nat) (output : List Bool) :
    ((RejectionSampling.trialWeights (leading++[true]) trials).map
      (Option.map (fun sample => Binary.encode width (Binary.value sample)))) (some output) ≤
    ((evalConfigWithin program
      (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7)+(13*width+18))).map
        (fun c => if c.halted then some c.outputBits else none)) (some output) := by
  classical
  rw [eval_after_trials before width leading hLeading hWidth trials]
  rw [← RejectionSampling.Saved.eval_prepared_trials
    (List.replicate width (some true) ++ none::before) leading hLeading trials, PMF.map_comp,
    PMF.map_apply, PMF.bind_apply]
  let law := evalConfigWithin RejectionSampling.program (start before width (leading++[true]))
    (sampleSteps leading trials)
  apply ENNReal.tsum_le_tsum
  intro c
  by_cases hZero : law c = 0
  · have hZeroActual : (evalConfigWithin RejectionSampling.program
        (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true]))
        (RejectionSampling.preparationSteps (leading++[true])+trials*(10*(leading++[true]).length+7))) c = 0 := hZero
    simp only [hZeroActual, ite_self, zero_mul, le_refl]
  · have member : c ∈ law.support := (PMF.mem_support_iff ..).mpr hZero
    cases hHalt : c.halted with
    | false => simp [Function.comp_def, hHalt]
    | true =>
      obtain ⟨finish, hStopped, hBits, hEval⟩ := accepted_continuation before width leading hLeading hWidth
        trials c member hHalt
      simp only [Function.comp_def, hHalt, ↓reduceIte, Option.map_some]
      rw [show 13*width+18 = 13*width+18+0 by omega, hEval 0, PMF.pure_map]
      simp [hStopped, hBits, PMF.pure_apply]

/-- The linked sampler, physical padding, and actual caller halt have
linear expected transition count in the retained public width. This bound
includes every rejection and does not impose a finite worst-case budget. -/
theorem expectedSteps_le (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width) :
    expectedStepsFrom program
      (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true])) ≤
        (50*(width+1) : Nat) := by
  let bits := leading++[true]
  change bits.length ≤ width at hWidth
  let block := 10*bits.length+7
  let preparation := RejectionSampling.preparationSteps bits+(13*width+18)
  have : NeZero block := ⟨by dsimp [block]; omega⟩
  have h := expectedStepsFrom_le_of_timeout_blocks_after
    (p := program) (start := start before width bits) preparation block (2⁻¹)
    (fun trials => by
      have bound := timeout_after_trials_le before width leading hLeading hWidth trials
      have budget : preparation+trials*block =
          RejectionSampling.preparationSteps bits+trials*(10*bits.length+7)+(13*width+18) := by
        dsimp [preparation, block]; omega
      rw [budget]
      exact bound)
  norm_num at h
  apply h.trans
  have hPrep : RejectionSampling.preparationSteps bits ≤ 4*bits.length+10 := by
    unfold RejectionSampling.preparationSteps
    split_ifs <;> omega
  calc
    _ ≤ ((4*bits.length+10+(13*width+18)+2*block : Nat) : ℝ≥0∞) := by
      simp only [preparation, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      exact add_le_add (add_le_add (by exact_mod_cast hPrep) le_rfl) (by rw [mul_comm])
    _ ≤ ((50*(width+1) : Nat) : ℝ≥0∞) := by
      exact_mod_cast (by dsimp [block]; omega :
        4*bits.length+10+(13*width+18)+2*block ≤ 50*(width+1))

end Machine.ScalarSamplerContinuation.Saved
