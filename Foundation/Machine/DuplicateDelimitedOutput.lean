import Foundation.Machine.ContextualDelimiter
import Foundation.Machine.BitstringRewind
import Foundation.Machine.GuardedTrace

namespace Machine.DuplicateDelimitedOutput

private def rewindEntry : Nat := writeDelimited.length + 1
private def secondEntry : Nat := rewindEntry + rewindBitstring.length + 1
private def finalPc : Nat := secondEntry + writeDelimited.length + 1
private def first : Program := writeDelimited.asSubroutine 0 rewindEntry
private def second : Program := rewindBitstring.asSubroutine rewindEntry secondEntry

/-- Encode the same contiguous bit block twice, by writing one delimited
field, physically rewinding the retained input, and writing the second.
A reserved blank before the block protects the preceding caller data. -/
def program : Program := first ++ second ++ writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] writeDelimited
      (second ++ writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) rewindEntry := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first rewindBitstring
      (writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) secondEntry := by
  simp [program, second, first, rewindEntry, Program.withSubroutine,
    Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) writeDelimited [.halt] finalPc := by
  simp [program, first, second, rewindEntry, secondEntry, Program.withSubroutine,
    Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    rw [third_layout]
    have hIndex : finalPc = (first ++ second).length + writeDelimited.length + 1 + 0 := by
      simp [finalPc, secondEntry, rewindEntry, first, second, Program.asSubroutine_length, Nat.add_assoc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The generator is copied twice from the same actual stored segment.
Saved cells on both tapes and the arbitrary suffix beyond its blank remain
protected. The result appends two exact delimiter encodings. -/
theorem runs_bits (beforeInput beforeOutput tail : List (Option Bool)) (bits : List Bool) (blanks : Nat) :
    ∃ target used,
      RunsFor program (writeDelimitedContextStart (none::beforeInput) beforeOutput tail bits blanks) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { left := bits.reverse.map some ++ none::beforeInput, right := tail } ∧
      target.outputTape.Equivalent
        { left := (FiniteBitEncoding.delimit bits ++ FiniteBitEncoding.delimit bits).reverse.map some ++ beforeOutput,
          right := List.replicate ((blanks-(2*bits.length+1))-(2*bits.length+1)) none } := by
  let done₁ := writeDelimitedContextFinish (none::beforeInput) beforeOutput tail bits blanks
  have run₁ := writeDelimitedContext_runs (none::beforeInput) beforeOutput tail bits blanks
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted
    [] writeDelimited (second ++ writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) rewindEntry
    (Nat.zero_le _) rfl rfl
  have r₁ : RunsFor program (writeDelimitedContextStart (none::beforeInput) beforeOutput tail bits blanks)
      (done₁.resumeAt rewindEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  let rewound : Configuration :=
    { pc := 3, inputTape := ({ left := beforeInput, right := bits.map some ++ none::tail } : Tape).moveRight,
      outputTape := done₁.outputTape, halted := true }
  have run₂ := rewindScratch_runs_from beforeInput bits none tail done₁.outputTape
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted
    first rewindBitstring (writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) secondEntry
    (Nat.zero_le _) rfl rfl
  have r₂ : RunsFor program (done₁.resumeAt rewindEntry) (rewound.resumeAt secondEntry) v₂ := by
    rw [second_layout]
    simpa [first, rewindEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc, done₁, writeDelimitedContextFinish, rewound] using embedded₂
  let outputPrefix := (FiniteBitEncoding.delimit bits).reverse.map some ++ beforeOutput
  let remaining := blanks-(2*bits.length+1)
  have run₃ := writeDelimitedContext_runs (none::beforeInput) outputPrefix tail bits remaining
  obtain ⟨v₃, _, embedded₃⟩ := run₃.withSubroutine_halted
    (first ++ second) writeDelimited [.halt] finalPc (Nat.zero_le _) rfl rfl
  have hCall : rewound.resumeAt secondEntry =
      (writeDelimitedContextStart (none::beforeInput) outputPrefix tail bits remaining).rebasePc
        (first ++ second).length := by
    rw [writeDelimitedContextStart_layout]
    cases bits <;> simp [rewound, done₁, outputPrefix, remaining,
      writeDelimitedContextFinish, Configuration.rebasePc, Configuration.resumeAt, Tape.moveRight,
      first, second, rewindEntry, secondEntry, Program.asSubroutine_length, Nat.add_assoc]
  have r₃ : RunsFor program (rewound.resumeAt secondEntry)
      ((writeDelimitedContextFinish (none::beforeInput) outputPrefix tail bits remaining).resumeAt finalPc) v₃ := by
    rw [hCall, third_layout]
    exact embedded₃
  let result := (writeDelimitedContextFinish (none::beforeInput) outputPrefix tail bits remaining).resumeAt finalPc
  refine ⟨{ result with halted := true }, v₁+v₂+v₃+1,
    ((r₁.trans r₂).trans r₃).succ (final_step result rfl rfl), rfl, ?_, ?_⟩
  · exact Tape.Equivalent.refl _
  · have hOutput : result.outputTape =
        { left := (FiniteBitEncoding.delimit bits ++ FiniteBitEncoding.delimit bits).reverse.map some ++ beforeOutput,
          right := List.replicate ((blanks-(2*bits.length+1))-(2*bits.length+1)) none } := by
      simp [result, writeDelimitedContextFinish, Configuration.resumeAt, outputPrefix, remaining,
        List.reverse_append, List.map_append, List.append_assoc]
    rw [hOutput]
    exact Tape.Equivalent.refl _

/-- All scans stop on arbitrary finite physical tapes. Missing separators
can affect which block is copied, but cannot produce an unbounded loop. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 1000*(input.cells+output.cells+1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration) target used ∧ target.halted = true := by
  obtain ⟨written, u₁, hu₁, run₁, hHalt₁⟩ := writeDelimited_terminates_from_anyTape input output
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] writeDelimited (second ++ writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) rewindEntry
    (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (written.resumeAt rewindEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨rewound, u₂, hu₂, run₂, hHalt₂, _⟩ := rewindBitstring_terminates_from written.inputTape written.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first rewindBitstring (writeDelimited.asSubroutine secondEntry finalPc ++ [.halt]) secondEntry
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (written.resumeAt rewindEntry) (rewound.resumeAt secondEntry) v₂ := by
    rw [second_layout]
    simpa [first, rewindEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  obtain ⟨written₂, u₃, hu₃, run₃, hHalt₃⟩ := writeDelimited_terminates_from_anyTape rewound.inputTape rewound.outputTape
  obtain ⟨v₃, hv₃, embedded₃⟩ := run₃.withSubroutine_halted
    (first ++ second) writeDelimited [.halt] finalPc (Nat.zero_le _) rfl hHalt₃
  have r₃ : RunsFor program (rewound.resumeAt secondEntry) (written₂.resumeAt finalPc) v₃ := by
    rw [third_layout]
    simpa [first, second, rewindEntry, secondEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt, Nat.add_assoc] using embedded₃
  have hStorage₁ := GuardedCompiler.sourceStorage_le_of_run run₁
  have hStorage₂ := GuardedCompiler.sourceStorage_le_of_run run₂
  have hLeft : written.inputTape.left.length ≤ written.inputTape.cells := by
    simp only [Tape.cells]; omega
  refine ⟨{ written₂.resumeAt finalPc with halted := true }, v₁+v₂+v₃+1, ?_,
    ((r₁.trans r₂).trans r₃).succ (final_step _ rfl rfl), rfl⟩
  simp only [GuardedCompiler.sourceStorage] at hStorage₁ hStorage₂
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (3000*(raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hInput : (Tape.ofBits raw).cells ≤ raw.length+1 := by cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hOutput : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 3000*(m+1), (PolynomiallyBounded.const 3000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.DuplicateDelimitedOutput
