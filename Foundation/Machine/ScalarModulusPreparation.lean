import Foundation.Machine.ScalarModulusColumns
import Foundation.Machine.BitstringRewind

namespace Machine.ScalarModulusPreparation

private def separator : Program := [.moveRight .output, .halt]

/-- Generate a unary width counter from the actual columns, rewind those
columns, and copy the canonical modulus beyond a blank separator. The width
counter survives trimming and can later pad the sampled scalar. -/
def program : Program :=
  ((SecondColumnGather.counterProgram.followedBy rewindBitstring).followedBy separator).followedBy
    ScalarModulusColumns.program

private theorem separator_runs (input output : Tape) :
    RunsFor separator ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 1, halted := true, inputTape := input, outputTape := output.moveRight } : Configuration) 2 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let moved := { start with pc := 1, outputTape := output.moveRight }
  have one : Step separator start moved := by
    simp [Step, successors, next, separator, start, moved, Instruction.next,
      Configuration.advance, Configuration.updateTape]
  have two : Step separator moved { moved with halted := true } := by
    simp [Step, successors, next, separator, start, moved, Instruction.next]
  exact ((RunsFor.zero _).succ one).succ two

/-- Both the saved width and canonical modulus are produced by the same
finite code. The bound charges the two column scans, rewind, separator,
high-zero erasure, and subroutine control transitions. -/
theorem runs (first modulus : List Bool) (width q : Nat)
    (hFirst : first.length = width) (hModulus : modulus.length = width)
    (hPositive : q ≠ 0) (hFit : q < 2^width) :
    ∃ (target : Configuration) (used : Nat), used ≤ 30*width+18 ∧
      RunsFor program
        (Configuration.initial (BinaryColumnSlotFill.fullSlots first (Binary.encode width q) modulus))
        target used ∧ target.halted = true ∧
      target.outputTape.Equivalent
        { left := q.bits.reverse.map some ++ none :: List.replicate width (some true)
          right := List.replicate (width-q.bits.length) none } ∧
      target.inputTape.Equivalent
        { left := (BinaryColumnSlotFill.fullSlots first (Binary.encode width q) modulus).reverse.map some } := by
  let columns := (first.zip (Binary.encode width q)).zip modulus
  let bits := BinaryModularAddition.interleave columns
  let counter : Tape := { left := List.replicate width (some true) }
  have emptyLeft : ({ Tape.ofBits bits with left := [] } : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  have hColumns : columns.length = width := by simp [columns, hFirst, hModulus]
  have hBits : bits.length = 3*width := by
    change (BinaryColumnSlotFill.fullSlots first (Binary.encode width q) modulus).length = _
    simp [BinaryColumnSlotFill.fullSlots_length, hFirst, hModulus]
  let gathered : Configuration :=
    { pc := 13, halted := true, inputTape := { left := bits.reverse.map some }, outputTape := counter }
  have one : RunsFor SecondColumnGather.counterProgram (Configuration.initial bits) gathered (10*width+2) := by
    have rawRun := SecondColumnGather.runs_counter columns [] []
    change RunsFor SecondColumnGather.counterProgram
      ({ inputTape := { Tape.ofBits bits with left := [] }, outputTape := { left := [] } } : Configuration)
      ({ pc := 13, halted := true, inputTape := { left := bits.reverse.map some ++ [] },
         outputTape := { left := List.replicate columns.length (some true) ++ [] } } : Configuration) _ at rawRun
    simpa only [Configuration.initial, gathered, counter, hColumns, List.append_nil, emptyLeft] using rawRun
  have two : RunsFor rewindBitstring (gathered.resumeAt 0)
      (rewindBitstringFinish bits counter) (2*bits.length+4) := by
    simpa only [gathered, Configuration.resumeAt, rewindBitstringStart] using rewindBitstring_runs bits counter
  obtain ⟨u, hu, linked⟩ := one.followedBy two (Nat.zero_le _) rfl rfl rfl
  let rewound := { (rewindBitstringFinish bits counter).resumeAt
      (SecondColumnGather.counterProgram.length + rewindBitstring.length + 2) with halted := true }
  have hRewoundInput : rewound.inputTape.Equivalent (Tape.ofBits bits) :=
    rewindBitstringFinish_input_equivalent bits counter
  have three : RunsFor separator (rewound.resumeAt 0)
      ({ pc := 1, halted := true, inputTape := rewound.inputTape, outputTape := counter.moveRight } : Configuration) 2 := by
    simpa only [rewound, Configuration.resumeAt, rewindBitstringFinish] using
      separator_runs rewound.inputTape counter
  obtain ⟨v, hv, linked₂⟩ := linked.followedBy three (Nat.zero_le _) rfl rfl rfl
  let separated : Configuration :=
    { pc := (SecondColumnGather.counterProgram.followedBy rewindBitstring).length + separator.length + 2
      halted := true
      inputTape := rewound.inputTape
      outputTape := counter.moveRight }
  obtain ⟨canonical, z, hz, lastRun, hHalt, hInput, hOutput⟩ :=
    ScalarModulusColumns.runs first modulus width q []
      (none :: List.replicate width (some true)) hFirst hModulus hPositive hFit
  have layout :
      ({ inputTape := { Tape.ofBits bits with left := [] }
         outputTape := { left := none :: List.replicate width (some true) } } : Configuration).Equivalent
        (separated.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa only [emptyLeft, separated, Configuration.resumeAt] using hRewoundInput.symm
    · simp [separated, Configuration.resumeAt, counter, Tape.moveRight]
      exact Tape.Equivalent.refl _
  obtain ⟨actual, actualRun, hActual⟩ := lastRun.exists_equivalent layout
  have hActualHalt : actual.halted = true := hActual.2.1.symm.trans hHalt
  obtain ⟨used, hUsed, run⟩ := linked₂.followedBy actualRun (Nat.zero_le _) rfl rfl hActualHalt
  refine ⟨{ actual.resumeAt
    (((SecondColumnGather.counterProgram.followedBy rewindBitstring).followedBy separator).length +
      ScalarModulusColumns.program.length + 2) with halted := true }, used, by omega, ?_, rfl, ?_, ?_⟩
  · simpa only [program, bits, columns, BinaryColumnSlotFill.fullSlots] using run
  · exact hActual.2.2.2.symm.trans (hOutput ▸ Tape.Equivalent.refl _)
  · simp only [List.append_nil] at hInput
    simpa only [Configuration.resumeAt, hInput] using hActual.2.2.1.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · exact Program.followedBy_no_randomBit _ _ SecondColumnGather.counter_no_randomBit rewindBitstring_no_randomBit
    · intro selected; simp [separator]
  · exact ScalarModulusColumns.no_randomBit

end Machine.ScalarModulusPreparation
