import Foundation.Crypto.Semantics.Machine.GuardedExecution
import Foundation.Examples.BitMachineExecution
import Foundation.Examples.MachinePolynomialTime

namespace Machine.Examples

open GuardedCompiler

/-- Arbitrary saved caller prefixes are retained in the entire compiled
distribution, not merely in the output projection of a selected trace. -/
example (source : Program) (input : List Bool) (q : Nat → Nat)
    (hHalt : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
      (traceBudget q input.length) =
      (evalConfigWithin source (Configuration.initial input) (q input.length)).map
        (encodeConfiguration source.length beforeInput beforeOutput) :=
  compile_initial_eval source input q hHalt beforeInput beforeOutput

example (source : Program) (input : List Bool) (q : Nat → Nat)
    (hHalt : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) (final : Configuration)
    (run : PaddedRunsFor (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
      final (traceBudget q input.length)) : final.halted = true :=
  compile_initial_all_branches_halted source input q hHalt beforeInput beforeOutput final run

example : traceBudget (fun _ => 2) 0 = 182 := rfl

/-- Both fair-bit outcomes are covered by the universal compiled halting
theorem. The 182-step bound includes padding after the actual halt. -/
example (beforeInput beforeOutput : List (Option Bool)) (final : Configuration)
    (run : PaddedRunsFor (compile randomOutputBit)
      (encodeConfiguration randomOutputBit.length beforeInput beforeOutput
        (Configuration.initial [])) final 182) : final.halted = true :=
  compile_initial_all_branches_halted randomOutputBit [] (fun _ => 2)
    randomOutputBit_haltsWithin beforeInput beforeOutput final run

example (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile randomOutputBit)
      (encodeConfiguration randomOutputBit.length beforeInput beforeOutput (Configuration.initial []))
      182 = (evalConfigWithin randomOutputBit (Configuration.initial []) 2).map
        (encodeConfiguration randomOutputBit.length beforeInput beforeOutput) :=
  compile_initial_eval randomOutputBit [] (fun _ => 2) randomOutputBit_haltsWithin
    beforeInput beforeOutput

/-- A raw input is operationally prepared before the source starts. The
code contains only the original finite machine instructions. -/
example : (initializedCompile randomOutputBit).length = 226 := rfl

example : evalConfigWithin (initializedCompile randomOutputBit) (Configuration.initial []) 42 =
    PMF.pure ((encodeConfiguration randomOutputBit.length [] [] (preparedSource [])).rebasePc 87) :=
  initializedCompile_prepare_eval randomOutputBit []

example : HaltsWithin (initializedCompile randomOutputBit) [] 225 :=
  initializedCompile_haltsWithin randomOutputBit [] (fun _ => 2) randomOutputBit_haltsWithin

example : HaltsWithin (initializedCompile randomOutputBit) [true, false, true] 522 :=
  initializedCompile_haltsWithin randomOutputBit [true, false, true] (fun _ => 2)
    (randomOutputBit_haltsWithin_any _)

/-- This assertion quantifies over all raw finite inputs and both random
outcomes. It includes tape preparation and the caller's final halt. The
output still uses the guarded encoding; it is not a raw-output simulator. -/
example : PolynomialTime (initializedCompile randomOutputBit) :=
  initializedCompile_polynomialTime randomOutputBit randomOutputBit_polynomialTime

example (source : Program) (h : PolynomialTime source) :
    PolynomialTime (initializedCompile source) := initializedCompile_polynomialTime source h

example (input : List Bool) (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile randomOutputBit)
      (encodeConfiguration randomOutputBit.length beforeInput beforeOutput (preparedSource input))
      (preparedTraceBudget (fun _ => 2) input.length) =
      (evalConfigWithin randomOutputBit (preparedSource input) 2).map
        (encodeConfiguration randomOutputBit.length beforeInput beforeOutput) :=
  compile_prepared_eval randomOutputBit input (fun _ => 2)
    (randomOutputBit_haltsWithin_any input) beforeInput beforeOutput

example (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    (evalConfigWithin (initializedCompile source) (Configuration.initial input)
      (31 * input.length + 42 + preparedTraceBudget q input.length + 1)).map
        Configuration.outputBits =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (encodeConfiguration source.length (input.reverse.map some) [] c).outputBits) :=
  initializedCompile_output_eval source input q halts

/-- Both fair-bit outcomes occur in the actual raw-input initialized
machine. The physical output contains guard `01` and data word `1b`, which
also makes explicit why raw output extraction remains necessary. -/
example : (evalConfigWithin (initializedCompile randomOutputBit) (Configuration.initial []) 225).map
    Configuration.outputBits =
      Foundation.Probability.sampleBit.map (fun bit => [false, true, true, bit]) := by
  change (evalConfigWithin (initializedCompile randomOutputBit) (Configuration.initial [])
    (31 * ([] : List Bool).length + 42 + preparedTraceBudget (fun _ => 2) ([] : List Bool).length + 1)).map
      Configuration.outputBits = _
  rw [initializedCompile_output_eval randomOutputBit [] (fun _ => 2) randomOutputBit_haltsWithin]
  change (((PMF.pure (Configuration.initial [])).bind (stepPMF randomOutputBit)).bind
      (stepPMF randomOutputBit)).map
        (fun c => (encodeConfiguration randomOutputBit.length [] [] c).outputBits) = _
  rw [PMF.pure_bind, randomOutputBit_stepPMF, PMF.bind_map, PMF.map_bind]
  have hBranch (bit : Bool) :
      (stepPMF randomOutputBit (randomNext bit)).map
        (fun c => (encodeConfiguration randomOutputBit.length [] [] c).outputBits) =
        PMF.pure [false, true, true, bit] := by
    cases bit <;> simp [PMF.pure_map, stepPMF, next, Instruction.next,
      randomOutputBit, randomNext, encodeConfiguration, encodeTape, VirtualCell.pairTape,
      VirtualCell.code, VirtualCell.encodedCells, VirtualCell.encodedLeftCells,
      Configuration.outputBits, Tape.bits]
  simp only [Function.comp_def]
  simp_rw [hBranch]
  simpa only [Function.comp_def] using
    (PMF.bind_pure_comp (p := Foundation.Probability.sampleBit)
      (f := fun bit => [false, true, true, bit]))

end Machine.Examples
