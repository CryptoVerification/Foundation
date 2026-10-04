import Foundation.Machine.ConsumedInputErasure
import Foundation.Machine.BitstringCopy
import Foundation.Machine.BitstringRewind
import Foundation.Machine.GuardedTrace

namespace Machine.ProductColumnTransfer

private def firstReturn : Nat := copyBitstring.swapTapes.length + 1
private def secondReturn : Nat := firstReturn + eraseOutputBlock.length + 1
private def finalReturn : Nat := secondReturn + rewindBitstring.length + 1
private def first : Program := copyBitstring.swapTapes.asSubroutine 0 firstReturn
private def second : Program := eraseOutputBlock.asSubroutine firstReturn secondReturn

/-- Move a prepared output-column block onto a clean input tape, erase the
old output copy, and rewind the input to the first arithmetic bit. -/
def program : Program :=
  first ++ second ++ rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] copyBitstring.swapTapes
      (second ++ rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first eraseOutputBlock
      (rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
      secondReturn := by
  simp [program, second, first, firstReturn,
    Program.withSubroutine, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) rewindBitstring [.halt] finalReturn := by
  simp [program, Program.withSubroutine, second, secondReturn,
    first, firstReturn, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [third_layout]
    have hOffset : finalReturn = (first ++ second).length +
        rewindBitstring.length + 1 + 0 := by
      simp [finalReturn, secondReturn, firstReturn, first, second,
        Program.asSubroutine_length, Nat.add_assoc]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

theorem runs (bits : List Bool) :
    ∃ target used,
      used ≤ 12 * bits.length + 12 ∧
      RunsFor program (Configuration.initial bits).swapTapes target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits bits) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  let copied := (copyBitstringFinish bits).swapTapes
  have hCopy := (copyBitstring_runs bits).swapTapes
  obtain ⟨v1, hv1, embedded1⟩ := hCopy.withSubroutine_halted
    [] copyBitstring.swapTapes
    (second ++ rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl rfl
  have r1 : RunsFor program (Configuration.initial bits).swapTapes
      (copied.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa [copied, Configuration.rebasePc] using embedded1
  let eraseStart := eraseOutputBlockStart copied.inputTape [] bits []
  let eraseFinish := eraseOutputBlockFinish copied.inputTape [] bits []
  have hErasure := eraseOutputBlock_runs copied.inputTape [] bits []
  let actualEraseStart : Configuration :=
    { inputTape := copied.inputTape, outputTape := copied.outputTape }
  have hEraseStart : eraseStart.Equivalent actualEraseStart := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    have hOuter := ConsumedInputErasure.outer_blank bits
    have hEraseTape : eraseStart.outputTape =
        ({ left := bits.reverse.map some ++ [none] } : Tape) := rfl
    rw [hEraseTape]
    simpa [actualEraseStart, copied, copyBitstringFinish,
      Configuration.swapTapes] using hOuter.symm
  obtain ⟨actualErased, actualEraseRun, hEraseEquiv⟩ :=
    hErasure.exists_equivalent hEraseStart
  have hActualHalt2 : actualErased.halted = true := hEraseEquiv.2.1.symm.trans rfl
  obtain ⟨v2, hv2, embedded2⟩ := actualEraseRun.withSubroutine_halted
    first eraseOutputBlock
    (rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hActualHalt2
  have hJoin2 : copied.resumeAt firstReturn =
      actualEraseStart.rebasePc first.length := by
    simp [actualEraseStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (copied.resumeAt firstReturn)
      (actualErased.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let rewindStart := rewindBitstringStart bits actualErased.outputTape
  let rewindFinish := rewindBitstringFinish bits actualErased.outputTape
  let actualRewindStart : Configuration :=
    { inputTape := actualErased.inputTape, outputTape := actualErased.outputTape }
  have hRewindStart : rewindStart.Equivalent actualRewindStart := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    have hInput : copied.inputTape.Equivalent actualErased.inputTape := by
      have hPreserved : eraseFinish.inputTape = copied.inputTape := rfl
      rw [← hPreserved]
      exact hEraseEquiv.2.2.1
    simpa [rewindStart, rewindBitstringStart, copied, copyBitstringFinish,
      Configuration.swapTapes, actualRewindStart] using hInput
  obtain ⟨actualRewound, actualRewindRun, hRewindEquiv⟩ :=
    (rewindBitstring_runs bits actualErased.outputTape).exists_equivalent hRewindStart
  have hActualHalt3 : actualRewound.halted = true := hRewindEquiv.2.1.symm.trans rfl
  obtain ⟨v3, hv3, embedded3⟩ := actualRewindRun.withSubroutine_halted
    (first ++ second) rewindBitstring [.halt] finalReturn
    (Nat.zero_le _) rfl hActualHalt3
  have hJoin3 : actualErased.resumeAt secondReturn =
      actualRewindStart.rebasePc (first ++ second).length := by
    simp [actualRewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (actualErased.resumeAt secondReturn)
      (actualRewound.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (actualRewound.resumeAt finalReturn)
      { actualRewound.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ actualRewound.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, ?_, ((r1.trans r2).trans r3).succ hStop,
    rfl, ?_, ?_⟩
  · have hCopySteps := copyBitstringSteps_le bits
    omega
  · have hInput := hRewindEquiv.2.2.1.symm.trans
      (rewindBitstringFinish_input_equivalent bits actualErased.outputTape)
    simpa [Configuration.resumeAt] using hInput
  · have hOutput : eraseFinish.outputTape.Equivalent ({} : Tape) := by
      change ({ right := List.replicate (bits.reverse.length + 1) none ++ [] } : Tape).Equivalent
        ({} : Tape)
      simpa using Tape.blank_padding_equivalent [] (bits.length + 1)
    have hActualOutput : actualErased.outputTape.Equivalent ({} : Tape) :=
      hEraseEquiv.2.2.2.symm.trans hOutput
    have hPreserved : actualRewound.outputTape.Equivalent actualErased.outputTape := by
      simpa [rewindFinish, rewindBitstringFinish] using hRewindEquiv.2.2.2.symm
    simpa [Configuration.resumeAt] using hPreserved.trans hActualOutput

/-- The transfer code terminates on arbitrary finite physical tapes. On a
malformed request this theorem makes no claim that the copied cells form a
canonical raw arithmetic input. -/
theorem runs_any_with_boundary (input output : Tape) :
    ∃ target used before,
      used ≤ 1000 * (input.cells + output.cells + 1) ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧
      target.inputTape.left = none :: before := by
  let start : Configuration := { inputTape := input, outputTape := output }
  obtain ⟨copiedCore, u1, hu1, copyRun, hHalt1⟩ :=
    copyBitstring_terminates_from_anyTape output input
  let copied := copiedCore.swapTapes
  have hCopy : RunsFor copyBitstring.swapTapes start copied u1 := by
    simpa [start, copied, Configuration.swapTapes] using copyRun.swapTapes
  obtain ⟨v1, hv1, embedded1⟩ := hCopy.withSubroutine_halted
    [] copyBitstring.swapTapes
    (second ++ rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl (by simpa [copied, Configuration.swapTapes] using hHalt1)
  have r1 : RunsFor program start (copied.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let eraseStart : Configuration :=
    { inputTape := copied.inputTape, outputTape := copied.outputTape }
  obtain ⟨erased, u2, hu2, eraseRun, hHalt2, _, _⟩ :=
    eraseOutputBlock_terminates_from_anyTape copied.inputTape copied.outputTape
  obtain ⟨v2, hv2, embedded2⟩ := eraseRun.withSubroutine_halted
    first eraseOutputBlock
    (rewindBitstring.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hHalt2
  have hJoin2 : copied.resumeAt firstReturn =
      eraseStart.rebasePc first.length := by
    simp [eraseStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (copied.resumeAt firstReturn)
      (erased.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let rewindStart : Configuration :=
    { inputTape := erased.inputTape, outputTape := erased.outputTape }
  obtain ⟨rewound, bits, before, hBits, rewindRun, hHalt3, hRewindLayout, _⟩ :=
    rewindBitstring_terminates_with_layout erased.inputTape erased.outputTape
  let u3 := 2 * bits.length + 4
  have hu3 : u3 ≤ 2 * erased.inputTape.left.length + 4 := by
    dsimp [u3]
    omega
  obtain ⟨v3, hv3, embedded3⟩ := rewindRun.withSubroutine_halted
    (first ++ second) rewindBitstring [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt3
  have hJoin3 : erased.resumeAt secondReturn =
      rewindStart.rebasePc (first ++ second).length := by
    simp [rewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (erased.resumeAt secondReturn)
      (rewound.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (rewound.resumeAt finalReturn)
      { rewound.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hStorage1 := GuardedCompiler.sourceStorage_le_of_run hCopy
  have hStorage2 := GuardedCompiler.sourceStorage_le_of_run eraseRun
  have hOutput2 : copied.outputTape.left.length ≤ copied.outputTape.cells := by
    simp [Tape.cells]
    omega
  have hInput3 : erased.inputTape.left.length ≤ erased.inputTape.cells := by
    simp [Tape.cells]
    omega
  refine ⟨{ rewound.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, before, ?_, ((r1.trans r2).trans r3).succ hStop,
    rfl, ?_⟩
  change copied.inputTape.cells + copied.outputTape.cells ≤
    input.cells + output.cells + u1 at hStorage1
  change erased.inputTape.cells + erased.outputTape.cells ≤
    copied.inputTape.cells + copied.outputTape.cells + u2 at hStorage2
  omega
  · change rewound.inputTape.left = none :: before
    rw [hRewindLayout]
    rfl

theorem runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 1000 * (input.cells + output.cells + 1) ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, hUsed, run, hHalt, _⟩ :=
    runs_any_with_boundary input output
  exact ⟨target, used, hUsed, run, hHalt⟩

end Machine.ProductColumnTransfer
