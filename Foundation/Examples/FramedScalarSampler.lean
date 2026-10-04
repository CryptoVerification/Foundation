import Foundation.Machine.FramedScalarSampler

namespace Foundation.Examples.FramedScalarSampler

open Machine
open scoped ENNReal

/-- A full native branch reads the framed p=7,q=3,g=2 request, draws the
accepted candidate 1, reads the saved six-cell width counter, and returns
the actual fixed-width code for 1. No mathematical post-decoder is used. -/
example : ∃ (target : Configuration) (used : Nat),
    used ≤ Machine.FramedScalarInput.validBudget 3 (Binary.encode 6 7) (Binary.encode 6 2) + 142 ∧
    RunsFor Machine.FramedScalarSampler.program
      (Configuration.initial (encodeSecurityParameter 3 ++
        frame (Binary.encode 6 7 ++ Binary.encode 6 3 ++ Binary.encode 6 2))) target used ∧
    target.halted = true ∧ target.outputBits = Binary.encode 6 1 := by
  let draw : Fin ([true]++[true]).length → Bool := fun i => decide (i.val = 0)
  obtain ⟨accepted, u, hu, sourceRun, sourceHalt, sourceInput, sourceOutput⟩ :=
    RejectionSampling.Saved.runs_first_trial (List.replicate 6 (some true)) [true]
      (by decide) draw (by decide)
  have sampleLength : (List.ofFn draw).length ≤ 6 := by simp [draw]
  obtain ⟨target, used, hUsed, run, hHalt, hOutput⟩ := Machine.FramedScalarSampler.runs_from_sample
    3 (Binary.encode 6 7) (Binary.encode 6 2) 3 (by simp) (by decide) (by decide)
    (List.ofFn draw) sampleLength accepted u sourceRun sourceHalt sourceInput sourceOutput
  have hSourceBound : u ≤ 45 := by simpa [RejectionSampling.preparationSteps] using hu
  have hValue : Binary.value (List.ofFn draw) = 1 := by decide
  exact ⟨target, used, by omega, run, hHalt, hValue ▸ hOutput⟩

/-- Saved caller data has no effect on the finite exact retry weights.
This example is the sampler's contextual law, not yet the linked framed
program's eventual output distribution. -/
example (before : List (Option Bool)) (trials : Nat) :
    (evalConfigWithin RejectionSampling.program
      (RejectionSampling.Saved.initial before [true,true]) (18+trials*27)).map
        (fun c => if c.halted then some c.outputBits else none) =
      RejectionSampling.trialWeights [true,true] trials := by
  simpa [RejectionSampling.preparationSteps] using
    RejectionSampling.Saved.eval_prepared_trials before [true] (by decide) trials

/-- The q=3 contextual sampler retains its 72-transition expectation bound
regardless of the caller data saved behind its protective blank. -/
example (before : List (Option Bool)) :
    RejectionSampling.Saved.expectedTransitions before [true,true] ≤ (72 : ℝ≥0∞) := by
  simpa using RejectionSampling.Saved.expectedTransitions_canonical before [true] (by decide)

/-- Even the unbounded exact distribution retains all saved caller data.
This is still the sampler invocation law, rather than the whole framed
caller's distribution after its native return and padding continuation. -/
example (before : List (Option Bool)) (output : List Bool) :
    RejectionSampling.Saved.eventualOutputMass before [true,true] output =
      ((Foundation.Probability.uniform (Fin 3)).map
        (fun a => Binary.encode 2 a.val)) output := by
  let : Nonempty (Fin (Binary.value ([true]++[true]))) := ⟨⟨0, by decide⟩⟩
  simpa only [List.cons_append, List.nil_append, List.length_cons, List.length_nil, Binary.value, Bool.toNat_true, ite_true, Nat.reduceAdd, Nat.reduceMul] using RejectionSampling.Saved.eventualOutputMass_uniform before [true] (by decide) output

end Foundation.Examples.FramedScalarSampler
