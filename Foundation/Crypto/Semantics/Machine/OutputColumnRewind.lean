import Foundation.Crypto.Semantics.Machine.TwoFieldColumnSkip
import Foundation.Crypto.Semantics.Machine.BitstringRewind
import Foundation.Crypto.Semantics.Machine.TapeSwap

namespace Machine.OutputColumnRewind

private def source : Program := rewindBitstring.swapTapes
private def returnPc : Nat := source.length + 1

/-- Rewind a contiguous output block to its first cell. This is the same
four-instruction scan used by `toThird`, without the two final head moves. -/
def toFirst : Program := rewindBitstring.swapTapes

theorem toFirst_runs (bits : List Bool) (input : Tape) :
    ∃ used, used ≤ 2 * bits.length + 4 ∧
      RunsFor toFirst (rewindBitstringStart bits input).swapTapes
        (rewindBitstringFinish bits input).swapTapes used ∧
      (rewindBitstringFinish bits input).swapTapes.outputTape.Equivalent
        (Tape.ofBits bits) := by
  refine ⟨2 * bits.length + 4, le_refl _, ?_, ?_⟩
  · exact (rewindBitstring_runs bits input).swapTapes
  · exact rewindBitstringFinish_input_equivalent bits input

/-- Rewind the output tape from any finite physical state. -/
theorem toFirst_runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 2 * output.left.length + 4 ∧
      RunsFor toFirst
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧ target.inputTape = input := by
  obtain ⟨target, used, hUsed, run, hHalt, hPreserved⟩ :=
    rewindBitstring_terminates_from output input
  refine ⟨target.swapTapes, used, hUsed, ?_, ?_, ?_⟩
  · simpa [toFirst, Configuration.swapTapes] using run.swapTapes
  · simpa [Configuration.swapTapes] using hHalt
  · simpa [Configuration.swapTapes] using hPreserved

/-- Rewind a column block and position the head at its second cell. -/
def toSecond : Program :=
  Program.withSubroutine [] source [.moveRight .output, .halt] returnPc

theorem toSecond_runs (bits : List Bool) (input : Tape) :
    let target : Configuration :=
      { pc := 6, inputTape := input,
        outputTape := (rewindBitstringFinish bits input).swapTapes.outputTape.moveRight,
        halted := true }
    ∃ used, used ≤ 2 * bits.length + 6 ∧
      RunsFor toSecond (rewindBitstringStart bits input).swapTapes target used ∧
      target.outputTape.Equivalent (Tape.ofBits bits).moveRight := by
  dsimp only
  let atReturn := (rewindBitstringFinish bits input).swapTapes.resumeAt returnPc
  let afterMove : Configuration :=
    { atReturn with pc := 6, outputTape := atReturn.outputTape.moveRight }
  let target : Configuration := { afterMove with halted := true }
  obtain ⟨used, hUsed, embedded⟩ :=
    (rewindBitstring_runs bits input).swapTapes.withSubroutine_halted
      [] source [.moveRight .output, .halt] returnPc (Nat.zero_le _) rfl rfl
  have hMoveLookup : toSecond[5]? = some (.moveRight .output) := by decide
  have hHaltLookup : toSecond[6]? = some .halt := by decide
  have hPc5 : atReturn.pc = 5 := rfl
  have hActive5 : atReturn.halted = false := rfl
  have hMove : Step toSecond atReturn afterMove := by
    simp [Step, successors, next, afterMove, hPc5, hActive5,
      hMoveLookup, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hPc6 : afterMove.pc = 6 := rfl
  have hActive6 : afterMove.halted = false := hActive5
  have hHalt : Step toSecond afterMove target := by
    simp [Step, successors, next, target, hPc6, hActive6,
      hHaltLookup, Instruction.next]
  refine ⟨used + 2, by omega, ?_, ?_⟩
  · convert (embedded.succ hMove).succ hHalt using 1 <;>
      simp [toSecond, atReturn, target, afterMove,
        Configuration.resumeAt, Configuration.rebasePc,
        rewindBitstringFinish, Configuration.swapTapes]
  · simpa [target, afterMove, atReturn, Configuration.resumeAt,
      Configuration.swapTapes] using
      (rewindBitstringFinish_input_equivalent bits input).moveRight

/-- The second-slot positioning code terminates on arbitrary finite tapes. -/
theorem toSecond_runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 2 * output.left.length + 6 ∧
      RunsFor toSecond
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧ target.inputTape = input := by
  obtain ⟨rewound, u, hu, run, hHalt, hPreserved⟩ :=
    rewindBitstring_terminates_from output input
  have hSource : RunsFor source
      ({ inputTape := input, outputTape := output } : Configuration)
      rewound.swapTapes u := by
    simpa [source, Configuration.swapTapes] using run.swapTapes
  obtain ⟨v, hv, embedded⟩ := hSource.withSubroutine_halted
    [] source [.moveRight .output, .halt] returnPc
    (Nat.zero_le _) rfl (by simpa [Configuration.swapTapes] using hHalt)
  let atReturn := rewound.swapTapes.resumeAt returnPc
  let afterMove : Configuration :=
    { atReturn with pc := 6, outputTape := atReturn.outputTape.moveRight }
  let target : Configuration := { afterMove with halted := true }
  have hMoveLookup : toSecond[5]? = some (.moveRight .output) := by decide
  have hHaltLookup : toSecond[6]? = some .halt := by decide
  have hPc5 : atReturn.pc = 5 := rfl
  have hActive5 : atReturn.halted = false := rfl
  have hMove : Step toSecond atReturn afterMove := by
    simp [Step, successors, next, afterMove, hPc5, hActive5,
      hMoveLookup, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hPc6 : afterMove.pc = 6 := rfl
  have hActive6 : afterMove.halted = false := hActive5
  have hFinal : Step toSecond afterMove target := by
    simp [Step, successors, next, target, hPc6, hActive6,
      hHaltLookup, Instruction.next]
  refine ⟨target, v + 2, ?_, ?_, rfl, ?_⟩
  · omega
  · convert (embedded.succ hMove).succ hFinal using 1 <;>
      simp [toSecond, atReturn, target, afterMove,
        Configuration.resumeAt, Configuration.rebasePc,
        Configuration.swapTapes]
  · simpa [target, afterMove, atReturn,
      Configuration.resumeAt, Configuration.swapTapes] using hPreserved

theorem toSecond_haltsWithin (bits : List Bool) : HaltsWithin toSecond bits 6 := by
  obtain ⟨used, hUsed, run, _⟩ := toSecond_runs [] (Tape.ofBits bits)
  have hInitial : Configuration.initial bits =
      (rewindBitstringStart [] (Tape.ofBits bits)).swapTapes := by
    cases bits <;> rfl
  unfold HaltsWithin
  rw [hInitial]
  exact run.haltsFrom_of_no_randomBit rfl
    (by intro tape; cases tape <;> decide) (by simpa using hUsed)

theorem toSecond_polynomialTime : PolynomialTime toSecond :=
  ⟨fun _ => 6, PolynomiallyBounded.const 6, toSecond_haltsWithin⟩

/-- Rewind a contiguous output bit block and advance to the third cell of
its first three-cell column. The source rewind is a tape-relabeled finite
program, and both final head moves are native instructions. -/
def toThird : Program :=
  Program.withSubroutine [] source
    [.moveRight .output, .moveRight .output, .halt] returnPc

private theorem source_length : source.length = 4 := rfl
private theorem returnPc_eq : returnPc = 5 := rfl

private theorem extra_blank_getD (bits : List Bool) (i : Nat) :
    (bits.map some ++ [none, none, none]).getD i none =
      (bits.map some ++ [none]).getD i none := by
  induction bits generalizing i with
  | nil =>
      cases i with
      | zero => rfl
      | succ i =>
          cases i with
          | zero => rfl
          | succ i => cases i <;> rfl
  | cons bit rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.map_cons, List.cons_append,
            List.getD_cons_succ] using ih i

private theorem one_extra_blank_getD (bits : List Bool) (i : Nat) :
    (bits.map some ++ [none, none]).getD i none =
      (bits.map some ++ [none]).getD i none := by
  induction bits generalizing i with
  | nil =>
      cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  | cons bit rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.map_cons, List.cons_append,
            List.getD_cons_succ] using ih i

theorem toThird_runs (bits : List Bool) (input : Tape) :
    let rewound := (rewindBitstringFinish bits input).swapTapes
    let target : Configuration :=
      { pc := 7, inputTape := input,
        outputTape := rewound.outputTape.moveRight.moveRight,
        halted := true }
    ∃ used, used ≤ 2 * bits.length + 7 ∧
      RunsFor toThird
        (rewindBitstringStart bits input).swapTapes target used ∧
      target.outputTape.Equivalent (Tape.ofBits bits).moveRight.moveRight := by
  dsimp only
  let rewound := (rewindBitstringFinish bits input).swapTapes
  let atReturn := rewound.resumeAt returnPc
  let afterFirst : Configuration :=
    { atReturn with pc := 6, outputTape := atReturn.outputTape.moveRight }
  let afterSecond : Configuration :=
    { afterFirst with pc := 7, outputTape := afterFirst.outputTape.moveRight }
  let target : Configuration := { afterSecond with halted := true }
  obtain ⟨used, hUsed, rSource⟩ :=
    (rewindBitstring_runs bits input).swapTapes.withSubroutine_halted
      [] source [.moveRight .output, .moveRight .output, .halt]
      returnPc (Nat.zero_le _) rfl rfl
  have hLookup5 : toThird[5]? = some (.moveRight .output) := by
    simpa [toThird, source_length] using
      (Program.withSubroutine_getElem?_suffix [] source
        [.moveRight .output, .moveRight .output, .halt] returnPc 0)
  have hLookup6 : toThird[6]? = some (.moveRight .output) := by
    simpa [toThird, source_length] using
      (Program.withSubroutine_getElem?_suffix [] source
        [.moveRight .output, .moveRight .output, .halt] returnPc 1)
  have hLookup7 : toThird[7]? = some .halt := by
    simpa [toThird, source_length] using
      (Program.withSubroutine_getElem?_suffix [] source
        [.moveRight .output, .moveRight .output, .halt] returnPc 2)
  have hPc5 : atReturn.pc = 5 := by
    simp [atReturn, returnPc_eq, Configuration.resumeAt]
  have hActive5 : atReturn.halted = false := by
    simp [atReturn, Configuration.resumeAt]
  have hFirst : Step toThird atReturn afterFirst := by
    simp [Step, successors, next, afterFirst, hPc5, hActive5,
      hLookup5, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hPc6 : afterFirst.pc = 6 := rfl
  have hActive6 : afterFirst.halted = false := hActive5
  have hSecond : Step toThird afterFirst afterSecond := by
    simp [Step, successors, next, afterSecond, hPc6, hActive6,
      hLookup6, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hPc7 : afterSecond.pc = 7 := rfl
  have hActive7 : afterSecond.halted = false := hActive6
  have hHalt : Step toThird afterSecond target := by
    simp [Step, successors, next, target, hPc7, hActive7,
      hLookup7, Instruction.next]
  refine ⟨used + 3, by omega, ?_, ?_⟩
  · simpa [toThird, atReturn, rewound, target, afterSecond, afterFirst,
      Configuration.resumeAt, Configuration.rebasePc,
      Configuration.swapTapes, rewindBitstringStart,
      rewindBitstringFinish,
      Nat.add_assoc] using
        ((rSource.succ hFirst).succ hSecond).succ hHalt
  · have hRewind := rewindBitstringFinish_input_equivalent bits input
    simpa [target, afterSecond, afterFirst, atReturn, rewound,
      Configuration.resumeAt, Configuration.swapTapes] using
        hRewind.moveRight.moveRight

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ toThird := by
  cases tape <;> decide

theorem haltsWithin (bits : List Bool) : HaltsWithin toThird bits 7 := by
  obtain ⟨used, hUsed, run, _⟩ := toThird_runs [] (Tape.ofBits bits)
  have hInitial : Configuration.initial bits =
      (rewindBitstringStart [] (Tape.ofBits bits)).swapTapes := by
    cases bits <;> rfl
  unfold HaltsWithin
  rw [hInitial]
  exact run.haltsFrom_of_no_randomBit rfl no_randomBit (by simpa using hUsed)

theorem polynomialTime : PolynomialTime toThird :=
  ⟨fun _ => 7, PolynomiallyBounded.const 7, haltsWithin⟩

/-- After filling the third slot, two blank cells separate the head from
the last column. Move across both blanks, then rewind the whole column
block to its first cell. -/
def thirdBoundaryToFirst : Program :=
  Program.withSubroutine [.moveLeft .output, .moveLeft .output]
    source [.halt] 7

theorem thirdBoundaryToFirst_runs (bits : List Bool) (input : Tape) :
    let start : Configuration :=
      { inputTape := input, outputTape := { left := none :: none :: bits.reverse.map some } }
    ∃ target used, used ≤ 2 * bits.length + 9 ∧
      RunsFor thirdBoundaryToFirst start target used ∧
      target.halted = true ∧ target.inputTape = input ∧
      target.outputTape.Equivalent (Tape.ofBits bits) := by
  dsimp only
  let start : Configuration :=
    { inputTape := input, outputTape := { left := none :: none :: bits.reverse.map some } }
  let afterOne : Configuration :=
    { pc := 1, inputTape := input,
      outputTape := { left := none :: bits.reverse.map some, right := [none] } }
  let afterTwo : Configuration :=
    { pc := 2, inputTape := input,
      outputTape := { left := bits.reverse.map some, right := [none, none] } }
  have hOne : Step thirdBoundaryToFirst start afterOne := by
    simp [Step, successors, next, thirdBoundaryToFirst, start, afterOne,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Program.withSubroutine]
  have hTwo : Step thirdBoundaryToFirst afterOne afterTwo := by
    simp [Step, successors, next, thirdBoundaryToFirst, afterOne, afterTwo,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Program.withSubroutine]
  let returned : Configuration :=
    { pc := 3, inputTape := input,
      outputTape := ({ right := bits.map some ++ [none, none, none] } : Tape).moveRight,
      halted := true }
  let rewindStart : Configuration :=
    { inputTape := input,
      outputTape := { left := bits.reverse.map some, right := [none, none] } }
  have hSource : RunsFor source rewindStart returned (2 * bits.length + 4) := by
    simpa [source, rewindStart, returned, Configuration.swapTapes] using
      (rewindBitstring_runs_from bits none [none, none] input).swapTapes
  obtain ⟨used, hUsed, hEmbedded⟩ := hSource.withSubroutine_halted
    [.moveLeft .output, .moveLeft .output] source [.halt] 7
    (Nat.zero_le _) rfl rfl
  have hJoin : afterTwo = rewindStart.rebasePc 2 := rfl
  let atReturn := returned.resumeAt 7
  have hReturn : RunsFor thirdBoundaryToFirst afterTwo atReturn used := by
    rw [hJoin]
    simpa [thirdBoundaryToFirst, atReturn] using hEmbedded
  have hHalt : Step thirdBoundaryToFirst atReturn
      { atReturn with halted := true } := by
    have hLookup : thirdBoundaryToFirst[7]? = some .halt := by
      decide
    simp [Step, successors, next, atReturn, Configuration.resumeAt,
      hLookup, Instruction.next]
  have hTrace : RunsFor thirdBoundaryToFirst start
      { atReturn with halted := true } (used + 3) := by
    convert (((RunsFor.zero start).succ hOne).succ hTwo).trans hReturn |>.succ hHalt using 1;
      omega
  refine ⟨{ atReturn with halted := true }, used + 3, ?_, hTrace,
    rfl, ?_, ?_⟩
  · omega
  · rfl
  · have hPadding :
        ({ right := bits.map some ++ [none, none, none] } : Tape).Equivalent
          ({ right := bits.map some ++ [none] } : Tape) := by
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact extra_blank_getD bits i
    have h := hPadding.moveRight.trans
      (rewindBitstringFinish_input_equivalent bits input)
    simpa [atReturn, Configuration.resumeAt, returned,
      rewindBitstringFinish] using h

/-- The two boundary moves followed by the native rewind terminate on
arbitrary physical tapes. Internal blanks can change where the rewind ends. -/
theorem thirdBoundaryToFirst_runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 2 * output.left.length + 7 ∧
      RunsFor thirdBoundaryToFirst
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧ target.inputTape = input := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let one : Configuration :=
    { pc := 1, inputTape := input, outputTape := output.moveLeft }
  let two : Configuration :=
    { pc := 2, inputTape := input, outputTape := output.moveLeft.moveLeft }
  have hOne : Step thirdBoundaryToFirst start one := by
    simp [Step, successors, next, thirdBoundaryToFirst, start, one,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Program.withSubroutine]
  have hTwo : Step thirdBoundaryToFirst one two := by
    simp [Step, successors, next, thirdBoundaryToFirst, one, two,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Program.withSubroutine]
  obtain ⟨rewound, u, hu, run, hHalt, hPreserved⟩ :=
    rewindBitstring_terminates_from output.moveLeft.moveLeft input
  have hSource : RunsFor source
      ({ inputTape := input, outputTape := output.moveLeft.moveLeft } : Configuration)
      rewound.swapTapes u := by
    simpa [source, Configuration.swapTapes] using run.swapTapes
  obtain ⟨v, hv, embedded⟩ := hSource.withSubroutine_halted
    [.moveLeft .output, .moveLeft .output] source [.halt] 7
    (Nat.zero_le _) rfl (by simpa [Configuration.swapTapes] using hHalt)
  have hJoin : two =
      (({ inputTape := input, outputTape := output.moveLeft.moveLeft } : Configuration).rebasePc 2) := rfl
  have hMiddle : RunsFor thirdBoundaryToFirst two
      (rewound.swapTapes.resumeAt 7) v := by
    rw [hJoin]
    simpa [thirdBoundaryToFirst] using embedded
  have hFinal : Step thirdBoundaryToFirst (rewound.swapTapes.resumeAt 7)
      { rewound.swapTapes.resumeAt 7 with halted := true } := by
    have hLookup : thirdBoundaryToFirst[7]? = some .halt := by decide
    simp [Step, successors, next, Configuration.resumeAt,
      hLookup, Instruction.next]
  have hLeft : (output.moveLeft.moveLeft).left.length ≤ output.left.length := by
    cases output with
    | mk left current right =>
        cases left with
        | nil => simp [Tape.moveLeft]
        | cons x xs =>
            cases xs <;> simp [Tape.moveLeft] <;> omega
  refine ⟨{ rewound.swapTapes.resumeAt 7 with halted := true },
    v + 3, ?_, ?_, rfl, ?_⟩
  · omega
  · convert (((RunsFor.zero start).succ hOne).succ hTwo).trans hMiddle |>.succ hFinal using 1
    omega
  · simpa [Configuration.swapTapes, Configuration.resumeAt] using hPreserved

/-- A second-slot fill leaves one blank between the head and the final
column. Cross that blank, then rewind to the first column cell. -/
def secondBoundaryToFirst : Program :=
  Program.withSubroutine [.moveLeft .output] source [.halt] 6

theorem secondBoundaryToFirst_runs (bits : List Bool) (input : Tape) :
    let start : Configuration :=
      { inputTape := input, outputTape := { left := none :: bits.reverse.map some } }
    ∃ target used, used ≤ 2 * bits.length + 7 ∧
      RunsFor secondBoundaryToFirst start target used ∧
      target.halted = true ∧ target.inputTape = input ∧
      target.outputTape.Equivalent (Tape.ofBits bits) := by
  dsimp only
  let start : Configuration :=
    { inputTape := input, outputTape := { left := none :: bits.reverse.map some } }
  let afterMove : Configuration :=
    { pc := 1, inputTape := input,
      outputTape := { left := bits.reverse.map some, right := [none] } }
  have hMove : Step secondBoundaryToFirst start afterMove := by
    simp [Step, successors, next, secondBoundaryToFirst, start, afterMove,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Program.withSubroutine]
  let rewindStart : Configuration :=
    { inputTape := input,
      outputTape := { left := bits.reverse.map some, right := [none] } }
  let returned : Configuration :=
    { pc := 3, inputTape := input,
      outputTape := ({ right := bits.map some ++ [none, none] } : Tape).moveRight,
      halted := true }
  have hSource : RunsFor source rewindStart returned (2 * bits.length + 4) := by
    simpa [source, rewindStart, returned, Configuration.swapTapes] using
      (rewindBitstring_runs_from bits none [none] input).swapTapes
  obtain ⟨used, hUsed, hEmbedded⟩ := hSource.withSubroutine_halted
    [.moveLeft .output] source [.halt] 6 (Nat.zero_le _) rfl rfl
  have hJoin : afterMove = rewindStart.rebasePc 1 := rfl
  let atReturn := returned.resumeAt 6
  have hReturn : RunsFor secondBoundaryToFirst afterMove atReturn used := by
    rw [hJoin]
    simpa [secondBoundaryToFirst, atReturn] using hEmbedded
  have hHalt : Step secondBoundaryToFirst atReturn
      { atReturn with halted := true } := by
    have hLookup : secondBoundaryToFirst[6]? = some .halt := by decide
    simp [Step, successors, next, atReturn, Configuration.resumeAt,
      hLookup, Instruction.next]
  have hTrace : RunsFor secondBoundaryToFirst start
      { atReturn with halted := true } (used + 2) := by
    convert ((RunsFor.zero start).succ hMove).trans hReturn |>.succ hHalt using 1;
      omega
  refine ⟨{ atReturn with halted := true }, used + 2, by omega,
    hTrace, rfl, rfl, ?_⟩
  have hPadding :
      ({ right := bits.map some ++ [none, none] } : Tape).Equivalent
        ({ right := bits.map some ++ [none] } : Tape) := by
    refine ⟨rfl, fun _ => rfl, ?_⟩
    exact one_extra_blank_getD bits
  have h := hPadding.moveRight.trans
    (rewindBitstringFinish_input_equivalent bits input)
  simpa [atReturn, Configuration.resumeAt, returned,
    rewindBitstringFinish] using h

/-- The single boundary move and native rewind terminate on arbitrary
finite tapes, regardless of the shape of a malformed column block. -/
theorem secondBoundaryToFirst_runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 2 * output.left.length + 7 ∧
      RunsFor secondBoundaryToFirst
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧ target.inputTape = input := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let one : Configuration :=
    { pc := 1, inputTape := input, outputTape := output.moveLeft }
  have hMove : Step secondBoundaryToFirst start one := by
    simp [Step, successors, next, secondBoundaryToFirst, start, one,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Program.withSubroutine]
  obtain ⟨rewound, u, hu, run, hHalt, hPreserved⟩ :=
    rewindBitstring_terminates_from output.moveLeft input
  have hSource : RunsFor source
      ({ inputTape := input, outputTape := output.moveLeft } : Configuration)
      rewound.swapTapes u := by
    simpa [source, Configuration.swapTapes] using run.swapTapes
  obtain ⟨v, hv, embedded⟩ := hSource.withSubroutine_halted
    [.moveLeft .output] source [.halt] 6
    (Nat.zero_le _) rfl (by simpa [Configuration.swapTapes] using hHalt)
  have hJoin : one =
      (({ inputTape := input, outputTape := output.moveLeft } : Configuration).rebasePc 1) := rfl
  have hMiddle : RunsFor secondBoundaryToFirst one
      (rewound.swapTapes.resumeAt 6) v := by
    rw [hJoin]
    simpa [secondBoundaryToFirst] using embedded
  have hFinal : Step secondBoundaryToFirst (rewound.swapTapes.resumeAt 6)
      { rewound.swapTapes.resumeAt 6 with halted := true } := by
    have hLookup : secondBoundaryToFirst[6]? = some .halt := by decide
    simp [Step, successors, next, Configuration.resumeAt,
      hLookup, Instruction.next]
  have hLeft : output.moveLeft.left.length ≤ output.left.length := by
    cases output with
    | mk left current right =>
        cases left <;> simp [Tape.moveLeft]
  refine ⟨{ rewound.swapTapes.resumeAt 6 with halted := true },
    v + 2, ?_, ?_, rfl, ?_⟩
  · omega
  · convert ((RunsFor.zero start).succ hMove).trans hMiddle |>.succ hFinal using 1
    omega
  · simpa [Configuration.swapTapes, Configuration.resumeAt] using hPreserved

theorem toFirst_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ toFirst := by
  cases tape <;> simp [toFirst, rewindBitstring, Program.swapTapes, Instruction.swapTapes]

theorem secondBoundaryToFirst_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ secondBoundaryToFirst := by
  cases tape <;> simp [secondBoundaryToFirst, source, rewindBitstring, Program.swapTapes,
    Instruction.swapTapes, Program.withSubroutine, Program.asSubroutine, Instruction.asSubroutine]

end Machine.OutputColumnRewind
