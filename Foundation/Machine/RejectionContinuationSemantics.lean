import Foundation.Machine.SavedScalarSamplerContinuation
import Foundation.Machine.ConfigurationExpectation

namespace Machine.RejectionContinuation

open scoped ENNReal

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private def sampleSteps (leading : List Bool) (trials : Nat) : Nat :=
  RejectionSampling.preparationSteps (leading++[true]) + trials*(10*(leading++[true]).length+7)

private def start (before : List (Option Bool)) (width : Nat) (bits : List Bool) : Configuration :=
  RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) bits

def entry : Nat := RejectionSampling.program.length+1

private def returned (c : Configuration) : Configuration :=
  if c.halted then c.resumeAt entry else c.rebasePc 0

/-- A finite native continuation, with its real return jump and caller halt. -/
def program (tail : Program) : Program := RejectionSampling.program.followedBy tail


/-- The supplied contract is a theorem about evaluation of the actual
linked code. It includes the charged final halt and keeps every retry
branch in the underlying probability distribution. -/
def Completion (tail : Program) (encode : List Bool → List Bool) (charge : Nat)
    (before : List (Option Bool)) (width : Nat) (leading : List Bool) : Prop :=
  ∀ trials accepted,
    accepted ∈ (evalConfigWithin RejectionSampling.program
      (start before width (leading++[true])) (sampleSteps leading trials)).support →
    accepted.halted = true →
    ∃ finish : Configuration, finish.halted = true ∧ finish.outputBits = encode accepted.outputBits ∧
      ∀ extra, evalConfigWithin (program tail) (accepted.resumeAt entry) (charge+extra) = PMF.pure finish

private theorem invocation (tail : Program) (before : List (Option Bool)) (width : Nat) (bits : List Bool) (steps : Nat) :
    evalReturnWithin (program tail) entry (start before width bits) steps =
      (evalConfigWithin RejectionSampling.program (start before width bits) steps).map returned := by
  have layout : (program tail) = Program.withSubroutine [] RejectionSampling.program
      (tail.asSubroutine entry (entry+tail.length+1) ++ [.halt]) entry := by
    simp [program, Program.followedBy, Program.withSubroutine, entry, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [layout]
  have law := RejectionSampling.Saved.eval_invocation []
    (tail.asSubroutine entry (entry+tail.length+1) ++ [.halt]) entry
    (by intro pc hpc; simp only [List.length_nil, zero_add]; unfold entry; omega)
    (List.replicate width (some true) ++ none::before) bits steps
  have rebaseZero (c : Configuration) : c.rebasePc 0 = c := by cases c; simp [Configuration.rebasePc]
  change _ = (evalConfigWithin RejectionSampling.program (start before width bits) steps).map
    (fun d => if d.halted then d.resumeAt entry else d.rebasePc 0)
  simpa only [List.length_nil, rebaseZero, start] using law

/-- Whole native evaluation after the retry inspection budget and the
charged fixed-width continuation budget. Returned branches execute the
continuation; unreturned branches retain their actual running configurations. -/
theorem eval_after_trials (tail : Program) (encode : List Bool → List Bool) (charge : Nat) (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (complete : Completion tail encode charge before width leading) (trials : Nat) :
    (evalConfigWithin (program tail) (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before)
      (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7) + (charge))).map
        (fun c => if c.halted then some c.outputBits else none) =
      (evalConfigWithin RejectionSampling.program
        (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true]))
        (RejectionSampling.preparationSteps (leading++[true]) +
          trials*(10*(leading++[true]).length+7))).bind
        (fun c => (evalConfigWithin (program tail)
          (if c.halted then c.resumeAt entry else c.rebasePc 0) (charge)).map
            (fun d => if d.halted then some d.outputBits else none)) := by
  change (evalConfigWithin (program tail) (start before width (leading++[true]))
    (sampleSteps leading trials+(charge))).map report = _
  have stable : ∀ d ∈ (evalReturnWithin (program tail) entry (start before width (leading++[true]))
      (sampleSteps leading trials)).support,
      d.pc = entry → ∀ extra,
        (evalConfigWithin (program tail) d (charge+extra)).map report =
          (evalConfigWithin (program tail) d (charge)).map report := by
    intro d member hPc extra
    rw [invocation tail before] at member
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
      obtain ⟨finish, _, _, hEval⟩ := complete trials c hc hHalt
      simpa only [returned, hHalt, ↓reduceIte, Nat.add_zero] using
        congrArg (fun law : PMF Configuration => law.map report) ((hEval extra).trans (hEval 0).symm)
  rw [evalConfigWithin_after_return (program tail) entry _ (sampleSteps leading trials)
    (charge) report stable, invocation tail before, PMF.bind_map]
  rfl

/-- Padding and the actual caller halt add bounded work without increasing
the retry timeout probability. This is a statement about the linked native
(program tail), including branches which reject arbitrarily many times. -/
theorem timeout_after_trials_le (tail : Program) (encode : List Bool → List Bool) (charge : Nat) (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (complete : Completion tail encode charge before width leading) (trials : Nat) :
    ((evalConfigWithin (program tail) (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before)
      (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7) + (charge))).map
        (fun c => if c.halted then some c.outputBits else none)) none ≤ (2⁻¹ : ℝ≥0∞)^trials := by
  classical
  rw [eval_after_trials tail encode charge before width leading hLeading hWidth complete trials]
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
      obtain ⟨finish, hStopped, _, hEval⟩ := complete trials c member hHalt
      simp only [hHalt, ↓reduceIte]
      rw [show charge = charge+0 by omega, hEval 0, PMF.pure_map]
      simp [report, hHalt, hStopped, PMF.pure_apply]

/-- Each finite accepted part of the exact retry law appears, with its
full probability, in the native fixed-width output law after the charged
continuation. Timeout branches are retained rather than renormalized. -/
theorem accepted_output_after_trials_le (tail : Program) (encode : List Bool → List Bool) (charge : Nat) (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (complete : Completion tail encode charge before width leading)
    (trials : Nat) (output : List Bool) :
    ((RejectionSampling.trialWeights (leading++[true]) trials).map
      (Option.map (encode))) (some output) ≤
    ((evalConfigWithin (program tail)
      (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true]))
      (RejectionSampling.preparationSteps (leading++[true]) +
        trials*(10*(leading++[true]).length+7)+(charge))).map
        (fun c => if c.halted then some c.outputBits else none)) (some output) := by
  classical
  rw [eval_after_trials tail encode charge before width leading hLeading hWidth complete trials]
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
      obtain ⟨finish, hStopped, hBits, hEval⟩ := complete trials c member hHalt
      simp only [Function.comp_def, hHalt, ↓reduceIte, Option.map_some]
      rw [show charge = charge+0 by omega, hEval 0, PMF.pure_map]
      simp [hStopped, hBits, PMF.pure_apply]

/-- The linked sampler, physical padding, and actual caller halt have
linear expected transition count in the retained public width. This bound
includes every rejection and does not impose a finite worst-case budget. -/
theorem expectedSteps_le (tail : Program) (encode : List Bool → List Bool) (charge : Nat) (before : List (Option Bool)) (width : Nat) (leading : List Bool)
    (hLeading : leading ≠ []) (hWidth : (leading++[true]).length ≤ width)
    (complete : Completion tail encode charge before width leading) :
    expectedStepsFrom (program tail)
      (RejectionSampling.Saved.initial (List.replicate width (some true) ++ none::before) (leading++[true])) ≤
        (24*width+24+charge : Nat) := by
  let bits := leading++[true]
  change bits.length ≤ width at hWidth
  let block := 10*bits.length+7
  let preparation := RejectionSampling.preparationSteps bits+(charge)
  have : NeZero block := ⟨by dsimp [block]; omega⟩
  have h := expectedStepsFrom_le_of_timeout_blocks_after
    (p := (program tail)) (start := start before width bits) preparation block (2⁻¹)
    (fun trials => by
      have bound := timeout_after_trials_le tail encode charge before width leading hLeading hWidth complete trials
      have budget : preparation+trials*block =
          RejectionSampling.preparationSteps bits+trials*(10*bits.length+7)+(charge) := by
        dsimp [preparation, block]; omega
      rw [budget]
      exact bound)
  norm_num at h
  apply h.trans
  have hPrep : RejectionSampling.preparationSteps bits ≤ 4*bits.length+10 := by
    unfold RejectionSampling.preparationSteps
    split_ifs <;> omega
  calc
    _ ≤ ((4*bits.length+10+(charge)+2*block : Nat) : ℝ≥0∞) := by
      simp only [preparation, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      exact add_le_add (add_le_add (by exact_mod_cast hPrep) le_rfl) (by rw [mul_comm])
    _ ≤ ((24*width+24+charge : Nat) : ℝ≥0∞) := by
      exact_mod_cast (by dsimp [block]; omega :
        4*bits.length+10+(charge)+2*block ≤ 24*width+24+charge)

end Machine.RejectionContinuation
