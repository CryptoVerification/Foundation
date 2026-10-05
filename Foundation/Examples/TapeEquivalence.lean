import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Foundation.Crypto.Semantics.Machine.BitstringCopy
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

/-- Actual left/right head motion restores the input cells but leaves a
redundant represented blank to the left of the initial head. -/
def headRestoredInput (input : List Bool) : Configuration :=
  { Configuration.initial input with inputTape :=
      (Tape.ofBits input).moveLeft.moveRight }

theorem headRestoredInput_equivalent (input : List Bool) :
    (Configuration.initial input).Equivalent (headRestoredInput input) :=
  ⟨rfl, rfl, (Tape.moveLeft_moveRight_equivalent (Tape.ofBits input)).symm,
    Tape.Equivalent.refl _⟩

example (input : List Bool) : headRestoredInput input ≠ Configuration.initial input := by
  intro h
  have hLeft := congrArg (fun c : Configuration => c.inputTape.left) h
  cases input <;> simp [headRestoredInput, Configuration.initial,
    Tape.ofBits, Tape.moveLeft, Tape.moveRight] at hLeft

/-- These are genuine counted caller transitions. No representation cleanup
or free tape copy is inserted between the two moves and the call. -/
def headMotionPrefix : Program :=
  [.moveLeft .input, .moveRight .input, .jump 3]

example (source suffix : Program) (returnPc : Nat) (input : List Bool) :
    RunsFor (Program.withSubroutine headMotionPrefix source suffix returnPc)
      (Configuration.initial input) ((headRestoredInput input).rebasePc 3) 3 := by
  let first : Configuration :=
    { Configuration.initial input with
      pc := 1, inputTape := (Tape.ofBits input).moveLeft }
  let second : Configuration := { headRestoredInput input with pc := 2 }
  have hFirst : Step (Program.withSubroutine headMotionPrefix source suffix returnPc)
      (Configuration.initial input) first := by
    simp [Step, successors, next, Program.withSubroutine, headMotionPrefix,
      Instruction.next, Configuration.initial, Configuration.updateTape,
      Configuration.advance, first]
  have hSecond : Step (Program.withSubroutine headMotionPrefix source suffix returnPc)
      first second := by
    simp [Step, successors, next, Program.withSubroutine, headMotionPrefix,
      Instruction.next, Configuration.initial, Configuration.updateTape,
      Configuration.advance, first, second, headRestoredInput]
  have hCall : Step (Program.withSubroutine headMotionPrefix source suffix returnPc)
      second ((headRestoredInput input).rebasePc 3) := by
    simp [Step, successors, next, Program.withSubroutine, headMotionPrefix,
      Instruction.next, second, headRestoredInput, Configuration.initial,
      Configuration.rebasePc]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hFirst) hSecond) hCall

/-- The copying invocation has its original universal linear bound even
though the caller has prepared only equivalent, not structurally equal,
initial input tapes. -/
example (input : List Bool) : ReturnsWithin
    (Program.withSubroutine headMotionPrefix copyBitstring [.halt] 12)
    ((headRestoredInput input).rebasePc 3) 12 (6 * input.length + 2) := by
  simpa [headMotionPrefix] using
    (copyBitstring_haltsWithin input).withSubroutine_returnsWithin_of_equivalent
      headMotionPrefix copyBitstring [.halt] 12 (headRestoredInput_equivalent input)

example (input : List Bool) :
    (evalReturnWithin
      (Program.withSubroutine headMotionPrefix copyBitstring [.halt] 12) 12
      ((headRestoredInput input).rebasePc 3) (6 * input.length + 2)).map
        (fun c => if c.pc = 12 then some c.outputBits else none) =
      PMF.pure (some input) := by
  simpa [headMotionPrefix] using
    ((copyBitstring_haltsWithin input).withSubroutine_evalReturn_of_equivalent
      headMotionPrefix copyBitstring [.halt] 12
      (by intro pc hpc; simp [headMotionPrefix, copyBitstring] at hpc ⊢; omega)
      (headRestoredInput_equivalent input)).trans (copyBitstring_eval input)

/-- Both fair outcomes and their probabilities are also unchanged. -/
example : (evalReturnWithin
    (Program.withSubroutine headMotionPrefix randomOutputBit [.halt] 6) 6
    ((headRestoredInput []).rebasePc 3) 2).map
      (fun c => if c.pc = 6 then some c.outputBits else none) =
    Foundation.Probability.sampleBit.map (fun b => some [b]) := by
  simpa [headMotionPrefix] using
    (randomOutputBit_haltsWithin.withSubroutine_evalReturn_of_equivalent
      headMotionPrefix randomOutputBit [.halt] 6
      (by intro pc hpc; simp [headMotionPrefix, randomOutputBit] at hpc ⊢; omega)
      (headRestoredInput_equivalent [])).trans randomOutputBit_eval

/-- The observation theorem covers timeouts too, not only successful runs. -/
example (p : Program) (input : List Bool) (steps : Nat) :
    evalWithin p input steps =
      (evalConfigWithin p (headRestoredInput input) steps).map
        (fun c => if c.halted then some c.outputBits else none) :=
  (headRestoredInput_equivalent input).evalOutput p steps

end Machine.Examples
