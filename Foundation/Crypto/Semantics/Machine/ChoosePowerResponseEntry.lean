import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.UnaryInput
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChoosePowerResponseEntry

private def firstReturn : Nat := OutputColumnRewind.toFirst.length + 1
private def payloadPc : Nat := firstReturn + skipUnary.length + 1
private def first : Program := OutputColumnRewind.toFirst.asSubroutine 0 firstReturn

/-- Rewind the prepared arithmetic block and consume the response frame
header and tag. Tag/width acceptance is a separate preceding guard; this
routine only positions the physical heads for candidate copying. -/
def program : Program := Program.withSubroutine first skipUnary
  [.moveRight .input, .halt] payloadPc

private theorem first_layout : program =
    Program.withSubroutine [] OutputColumnRewind.toFirst
      (skipUnary.asSubroutine firstReturn payloadPc ++ [.moveRight .input, .halt]) firstReturn := by
  simp [program, first, firstReturn, Program.withSubroutine, Program.asSubroutine_length]

private theorem finish_steps (c : Configuration) (hPc : c.pc = payloadPc)
    (hActive : c.halted = false) :
    RunsFor program c
      { pc := payloadPc + 1, inputTape := c.inputTape.moveRight,
        outputTape := c.outputTape, halted := true } 2 := by
  have hLookup : program[payloadPc]? = some (.moveRight .input) := by
    have hIndex : payloadPc = first.length + skipUnary.length + 1 + 0 := by
      simp [payloadPc, firstReturn, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  have hLookup' : program[payloadPc+1]? = some .halt := by
    have hIndex : payloadPc+1 = first.length + skipUnary.length + 1 + 1 := by
      simp [payloadPc, firstReturn, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  let moved : Configuration :=
    { pc := payloadPc + 1, inputTape := c.inputTape.moveRight, outputTape := c.outputTape }
  have hMove : Step program c moved := by
    simp [Step, successors, next, moved, hPc, hActive, hLookup,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  have hHalt : Step program moved { moved with halted := true } := by
    simp [Step, successors, next, moved, hLookup', Instruction.next]
  exact ((RunsFor.zero c).succ hMove).succ hHalt

/-- A correctly framed choose response reaches its first delimited
candidate with the actual modulus/exponent block at the output head. The
entire response header and tag are retained on the input tape. -/
theorem runs_choose (before : List (Option Bool)) (columns body : List Bool) :
    let reply := false :: body
    let start : Configuration :=
      { inputTape := { Tape.ofBits (frame reply) with left := before },
        outputTape := { left := columns.reverse.map some } }
    ∃ target used, used ≤ 2 * columns.length + 3 * reply.length + 9 ∧
      RunsFor program start target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits body with left := some false :: some false :: List.replicate reply.length (some true) ++ before } ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let reply := false :: body
  let input : Tape := { Tape.ofBits (frame reply) with left := before }
  obtain ⟨u₁, hu₁, run₁, hOutput₁⟩ := OutputColumnRewind.toFirst_runs columns input
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] OutputColumnRewind.toFirst
    (skipUnary.asSubroutine firstReturn payloadPc ++ [.moveRight .input, .halt])
    firstReturn (Nat.zero_le _) rfl rfl
  let rewound := (rewindBitstringFinish columns input).swapTapes
  have r₁ : RunsFor program
      ({ inputTape := input, outputTape := { left := columns.reverse.map some } } : Configuration)
      (rewound.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa [rewindBitstringStart, rewound, Configuration.swapTapes,
      Configuration.rebasePc] using embedded₁
  have run₂ := skipUnary_runs before reply.length reply rewound.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted first skipUnary
    [.moveRight .input, .halt] payloadPc (Nat.zero_le _) rfl rfl
  have hCall : rewound.resumeAt firstReturn =
      (skipUnaryStart before reply.length reply rewound.outputTape).rebasePc first.length := by
    simp [rewound, input, rewindBitstringFinish, Configuration.swapTapes,
      Configuration.resumeAt, Configuration.rebasePc, skipUnaryStart,
      frame, encodeSecurityParameter, first, firstReturn, Program.asSubroutine_length]
  let after := skipUnaryFinish before reply.length reply rewound.outputTape
  have r₂ : RunsFor program (rewound.resumeAt firstReturn) (after.resumeAt payloadPc) v₂ := by
    rw [hCall]
    simpa only [program] using embedded₂
  let result : Configuration :=
    { pc := payloadPc+1, inputTape := after.inputTape.moveRight,
      outputTape := after.outputTape, halted := true }
  refine ⟨result, v₁+v₂+2, ?_, (r₁.trans r₂).trans (finish_steps _ rfl rfl), rfl, ?_, ?_⟩
  · dsimp only [reply] at hv₂
    omega
  · have hInput : result.inputTape =
        { Tape.ofBits body with left := some false :: some false :: List.replicate reply.length (some true) ++ before } := by
      cases body <;> simp [result, after, reply, skipUnaryFinish, Tape.ofBits, Tape.moveRight]
    rw [hInput]
    exact Tape.Equivalent.refl _
  · exact hOutput₁

/-- Finite physical tape bounds suffice for both scans, even with a
missing response terminator or malformed arithmetic block. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 100 * (input.cells + output.cells + 1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧ target.halted = true := by
  obtain ⟨rewound, u₁, hu₁, run₁, hHalt₁, hInput₁⟩ := OutputColumnRewind.toFirst_runs_any input output
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] OutputColumnRewind.toFirst
    (skipUnary.asSubroutine firstReturn payloadPc ++ [.moveRight .input, .halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (rewound.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨after, u₂, hu₂, run₂, hHalt₂, _⟩ :=
    skipUnary_terminates_from_anyTape rewound.inputTape rewound.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted first skipUnary
    [.moveRight .input, .halt] payloadPc (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (rewound.resumeAt firstReturn) (after.resumeAt payloadPc) v₂ := by
    simpa [program, first, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  refine ⟨_, v₁+v₂+2, ?_, (r₁.trans r₂).trans (finish_steps _ rfl rfl), rfl⟩
  rw [hInput₁] at hu₂
  simp only [Tape.cells] at hu₁ hu₂ ⊢
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (300 * (raw.length + 1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hCells : (Tape.ofBits raw).cells ≤ raw.length+1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 300 * (m + 1), (PolynomiallyBounded.const 300).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChoosePowerResponseEntry
