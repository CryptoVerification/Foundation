import Foundation.Machine.BinaryIsOneInPlace
import Foundation.Machine.OutputColumnRewind

namespace Machine.OutputIsOne

private def rewindReturn : Nat := OutputColumnRewind.toFirst.length + 1
private def checkReturn : Nat := rewindReturn + BinaryIsOneInPlace.program.length + 1
private def beforeCheck : Program :=
  OutputColumnRewind.toFirst.asSubroutine 0 rewindReturn

/-- Rewind a contiguous result on the output tape, then erase it in place
while deciding whether its binary value is one. Both stages are finite
machine code on the same physical tapes. -/
def program : Program :=
  beforeCheck ++
    BinaryIsOneInPlace.program.asSubroutine rewindReturn checkReturn ++ [.halt]

private theorem beforeCheck_length : beforeCheck.length = rewindReturn := by
  simp [beforeCheck, rewindReturn]

private theorem first_layout : program =
    Program.withSubroutine [] OutputColumnRewind.toFirst
      (BinaryIsOneInPlace.program.asSubroutine rewindReturn checkReturn ++ [.halt])
      rewindReturn := by
  simp [program, beforeCheck, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine beforeCheck BinaryIsOneInPlace.program [.halt]
      checkReturn := by
  simp [program, Program.withSubroutine, beforeCheck_length]

def budget (length : Nat) : Nat := 8 * (length + 1) + 10

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem halt_lookup : program[checkReturn]? = some .halt := by
  rw [second_layout]
  have hIndex : checkReturn = beforeCheck.length +
      BinaryIsOneInPlace.program.length + 1 + 0 := by
    simp [checkReturn, beforeCheck_length]
  rw [hIndex, Program.withSubroutine_getElem?_suffix]
  rfl

private theorem halt_step (c : Configuration) :
    Step program (c.resumeAt checkReturn)
      { c.resumeAt checkReturn with halted := true } := by
  simp [Step, successors, next, halt_lookup,
    Configuration.resumeAt, Instruction.next]

/-- Contextual operation on a genuine output block. The other tape may
contain any finite data. Blank padding represents no free tape operation. -/
theorem runs_from_block (bits : List Bool) (other output : Tape)
    (hOutput : output.Equivalent { left := bits.reverse.map some }) :
    ∃ finish used,
      used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := other, outputTape := output } : Configuration)
        finish used ∧
      finish.halted = true ∧ finish.outputBits =
        [BinaryIsOneInPlace.accepts bits] := by
  obtain ⟨rewindUsed, hRewindUsed, rewindRun, hRewindBits⟩ :=
    OutputColumnRewind.toFirst_runs bits other
  let rewindStart : Configuration :=
    (rewindBitstringStart bits other).swapTapes
  let actualStart : Configuration :=
    { inputTape := other, outputTape := output }
  have hStart : rewindStart.Equivalent actualStart :=
    ⟨rfl, rfl, Tape.Equivalent.refl _, hOutput.symm⟩
  obtain ⟨rewound, actualRewind, hRewindEq⟩ :=
    RunsFor.exists_equivalent (other := actualStart) rewindRun hStart
  have hRewoundHalt : rewound.halted = true := by
    exact hRewindEq.2.1.symm.trans rfl
  have hRewoundOutput : rewound.outputTape.Equivalent
      (Tape.ofBits bits) :=
    hRewindEq.2.2.2.symm.trans hRewindBits
  obtain ⟨checkTarget, checkUsed, hCheckUsed, checkRun,
    hCheckHalt, hCheckBits⟩ :=
    BinaryIsOneInPlace.runs_from_equivalent bits rewound.inputTape
      rewound.outputTape hRewoundOutput
  obtain ⟨firstUsed, hFirstUsed, embeddedFirst⟩ :=
    actualRewind.withSubroutine_halted [] OutputColumnRewind.toFirst
      (BinaryIsOneInPlace.program.asSubroutine rewindReturn checkReturn ++ [.halt])
      rewindReturn (Nat.zero_le _) rfl hRewoundHalt
  have firstRun : RunsFor program actualStart
      (rewound.resumeAt rewindReturn) firstUsed := by
    rw [first_layout]
    simpa [actualStart, Configuration.rebasePc] using embeddedFirst
  obtain ⟨secondUsed, hSecondUsed, embeddedSecond⟩ :=
    checkRun.withSubroutine_halted beforeCheck BinaryIsOneInPlace.program
      [.halt] checkReturn (Nat.zero_le _) rfl hCheckHalt
  have secondRun : RunsFor program (rewound.resumeAt rewindReturn)
      (checkTarget.resumeAt checkReturn) secondUsed := by
    rw [second_layout]
    simpa [beforeCheck_length, Configuration.resumeAt,
      Configuration.rebasePc] using embeddedSecond
  let final : Configuration :=
    { checkTarget.resumeAt checkReturn with halted := true }
  refine ⟨final, firstUsed + secondUsed + 1, ?_,
    (firstRun.trans secondRun).succ (halt_step checkTarget), rfl, ?_⟩
  · dsimp [budget]
    dsimp [BinaryIsOneInPlace.budget] at hCheckUsed
    omega
  · exact hCheckBits

end Machine.OutputIsOne
