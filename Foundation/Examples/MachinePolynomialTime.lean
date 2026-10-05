import Foundation.Crypto.Semantics.Machine.PolynomialTime
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

theorem haltImmediately_polynomialTime : PolynomialTime haltImmediately := by
  refine ⟨fun _ => 1, PolynomiallyBounded.const 1, ?_⟩
  intro input
  exact haltImmediately_haltsWithin input

/-- The copy program runs a branch, optional write and jump, then halt.
Padding makes the same four-step bound apply also to a blank input cell. -/
theorem copyOneBit_haltsWithin (input : List Bool) :
    HaltsWithin copyOneBit input 4 := by
  rw [haltsWithin_iff_reachableStates]
  cases input with
  | nil =>
      simp [reachableStates, paddedSuccessors, successors, next,
        Instruction.next, copyOneBit, Configuration.initial,
        Configuration.tape, Tape.ofBits]
  | cons b rest =>
      cases b <;>
        simp [reachableStates, paddedSuccessors, successors, next,
          Instruction.next, copyOneBit, Configuration.initial,
          Configuration.tape, Configuration.updateTape, Configuration.advance,
          Tape.ofBits, Tape.write]

theorem copyOneBit_polynomialTime : PolynomialTime copyOneBit := by
  refine ⟨fun _ => 4, PolynomiallyBounded.const 4, ?_⟩
  intro input
  exact copyOneBit_haltsWithin input

/-- Fair random output takes one random step and one halt step on every
input, regardless of the input bits. -/
theorem randomOutputBit_haltsWithin_any (input : List Bool) :
    HaltsWithin randomOutputBit input 2 := by
  rw [haltsWithin_iff_reachableStates]
  simp [reachableStates, paddedSuccessors, successors, next,
    Instruction.next, randomOutputBit, Configuration.initial,
    Configuration.updateTape, Configuration.advance,
    Tape.ofBits, Tape.write]

theorem randomOutputBit_polynomialTime : PolynomialTime randomOutputBit := by
  refine ⟨fun _ => 2, PolynomiallyBounded.const 2, ?_⟩
  intro input
  exact randomOutputBit_haltsWithin_any input

end Machine.Examples
