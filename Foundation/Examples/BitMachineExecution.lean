import Foundation.Crypto.Semantics.Machine.Execution
import Foundation.Examples.BitMachine

namespace Machine.Examples

/-- One halt instruction takes exactly one operational step. -/
example (input : List Bool) : HaltsWith haltImmediately input [] 1 := by
  refine ⟨{ (Configuration.initial input) with halted := true }, ?_, rfl, ?_⟩
  · apply RunsFor.succ (RunsFor.zero _)
    simp [Step, successors, next, haltImmediately, Configuration.initial,
      Instruction.next]
  · simp [Configuration.outputBits, Tape.bits, Configuration.initial]

theorem haltImmediately_haltsWithin (input : List Bool) :
    HaltsWithin haltImmediately input 1 :=
  haltInstruction_haltsWithin input

example (input : List Bool) :
    evalWithin haltImmediately input 1 = PMF.pure (some []) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
    haltImmediately, Configuration.initial, Configuration.outputBits,
    Tape.bits, PMF.pure_bind, PMF.pure_map]

/-- Two operational steps are a fair random write followed by halt. -/
theorem randomOutputBit_eval :
    evalWithin randomOutputBit [] 2 =
      Foundation.Probability.sampleBit.map (fun b => some [b]) := by
  unfold evalWithin
  change (((PMF.pure (Configuration.initial [])).bind
      (stepPMF randomOutputBit)).bind (stepPMF randomOutputBit)).map
      (fun c => if c.halted then some c.outputBits else none) = _
  rw [PMF.pure_bind, randomOutputBit_stepPMF, PMF.bind_map, PMF.map_bind]
  have hbranch (b : Bool) :
      (stepPMF randomOutputBit (randomNext b)).map
          (fun c => if c.halted then some c.outputBits else none) =
        PMF.pure (some [b]) := by
    cases b <;> simp [PMF.pure_map, stepPMF, next, Instruction.next,
      randomOutputBit, randomNext,
      Configuration.outputBits, Tape.bits]
  simp only [Function.comp_def]
  simp_rw [hbranch]
  simpa only [Function.comp_def] using
    (PMF.bind_pure_comp (p := Foundation.Probability.sampleBit)
      (f := fun b => some [b]))

theorem randomOutputBit_haltsWithin : HaltsWithin randomOutputBit [] 2 := by
  apply haltsWithin_of_no_timeout_support
  rw [randomOutputBit_eval]
  intro hNone
  rw [PMF.mem_support_map_iff] at hNone
  rcases hNone with ⟨b, _, hValue⟩
  cases hValue

example : Foundation.Probability.eventProb
    (evalWithin randomOutputBit [] 2) (· = none) = 0 :=
  evalWithin_no_timeout _ _ _ randomOutputBit_haltsWithin

example : Foundation.Probability.eventProb
    (evalWithin randomOutputBit [] 2) (· = some [true]) = 1 / 2 := by
  rw [randomOutputBit_eval]
  unfold Foundation.Probability.eventProb
  rw [PMF.toOuterMeasure_map_apply]
  have hpre : ((fun b : Bool => some [b]) ⁻¹' {some [true]}) = {true} := by
    ext b
    cases b <;> simp
  change Foundation.Probability.sampleBit.toOuterMeasure
    ((fun b : Bool => some [b]) ⁻¹' {some [true]}) = 1 / 2
  rw [hpre]
  simp [Foundation.Probability.sampleBit, Foundation.Probability.uniform]

end Machine.Examples
