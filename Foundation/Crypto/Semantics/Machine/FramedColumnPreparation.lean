import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedColumnPreparation

private def firstReturn : Nat := SecurityWidthTemplate.program.length + 1
private def finalReturn : Nat := firstReturn + OutputColumnRewind.toThird.length + 1
private def first : Program :=
  SecurityWidthTemplate.program.asSubroutine 0 firstReturn

/-- One fixed finite prefix creates the `n+3` column template and places
the output head at the third cell of its first row. The instance frame is
still on the input tape. Neither stage reconstructs a machine tape. -/
def program : Program :=
  Program.withSubroutine first OutputColumnRewind.toThird [.halt] finalReturn

private theorem first_layout : program =
    Program.withSubroutine [] SecurityWidthTemplate.program
      (OutputColumnRewind.toThird.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, first, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem second_layout : program =
    Program.withSubroutine first OutputColumnRewind.toThird [.halt] finalReturn := rfl

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [second_layout]
    have hOffset : finalReturn = first.length +
        OutputColumnRewind.toThird.length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

theorem runs_valid (n : Nat) (rest : List Bool) :
    let width := n + 3
    let bits := List.replicate (3 * width) false
    ∃ target used, used ≤ 9 * n + 21 + 2 * bits.length + 8 ∧
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++ rest)) target used ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        (Tape.ofBits (BinaryThirdColumnTemplate.columns
          (List.replicate width false))).moveRight.moveRight := by
  dsimp only
  let width := n + 3
  let bits := List.replicate (3 * width) false
  obtain ⟨afterWidth, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    SecurityWidthTemplate.runs_valid n rest
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] SecurityWidthTemplate.program
    (OutputColumnRewind.toThird.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ rest))
      (afterWidth.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  obtain ⟨v2, hv2, run2, hOutput2⟩ :=
    OutputColumnRewind.toThird_runs bits afterWidth.inputTape
  -- The rewind begins with exactly the cells written by the first stage.
  have hJoin : afterWidth.resumeAt firstReturn =
      ((rewindBitstringStart bits afterWidth.inputTape).swapTapes).rebasePc
        first.length := by
    simp [Configuration.resumeAt, Configuration.rebasePc,
      Configuration.swapTapes, rewindBitstringStart, hOutput1,
      first, firstReturn, Program.asSubroutine_length,
      bits, width, List.map_replicate]
  let afterRewind : Configuration :=
    { pc := 7, inputTape := afterWidth.inputTape,
      outputTape :=
        ((rewindBitstringFinish bits afterWidth.inputTape).swapTapes).outputTape.moveRight.moveRight,
      halted := true }
  obtain ⟨v2', hv2', embedded2⟩ := run2.withSubroutine_halted
    first OutputColumnRewind.toThird [.halt] finalReturn
    (Nat.zero_le _) rfl rfl
  have r2 : RunsFor program
      (afterWidth.resumeAt firstReturn)
      (afterRewind.resumeAt finalReturn) v2' := by
    rw [hJoin]
    simpa [second_layout, afterRewind] using embedded2
  have hFinal : Step program (afterRewind.resumeAt finalReturn)
      { afterRewind.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ afterRewind.resumeAt finalReturn with halted := true },
    v1 + v2' + 1, ?_, (r1.trans r2).succ hFinal, rfl, ?_, ?_⟩
  · change v1 + v2' + 1 ≤ 9 * n + 21 + 2 * bits.length + 8
    omega
  · simpa [afterRewind, Configuration.resumeAt] using hInput1
  · have hBits : bits = BinaryThirdColumnTemplate.columns
        (List.replicate width false) := SecurityWidthTemplate.blankColumns width
    simpa [afterRewind, Configuration.resumeAt, hBits] using hOutput2

/-- The first framed-column wrapper also terminates when the unary security
parameter is malformed or unterminated. Its physical output is still a
finite three-cell-per-column template. -/
theorem runs_any_layout (raw : List Bool) :
    ∃ target used width rest before,
      used ≤ 16 * (raw.length + 1) + 100 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits rest with left := before } ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate (3 * width) false)).moveRight.moveRight ∧
      width ≤ raw.length + 3 ∧ rest.length ≤ raw.length := by
  obtain ⟨afterWidth, u1, width, rest, before, hu1, hw, run1,
    hHalt1, hInput1, hOutput1, hRest⟩ := SecurityWidthTemplate.runs_any_layout raw
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] SecurityWidthTemplate.program
    (OutputColumnRewind.toThird.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (afterWidth.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let bits := List.replicate (3 * width) false
  obtain ⟨u2, hu2, rewindRun, hOutput2⟩ :=
    OutputColumnRewind.toThird_runs bits afterWidth.inputTape
  have hJoin : afterWidth.resumeAt firstReturn =
      ((rewindBitstringStart bits afterWidth.inputTape).swapTapes).rebasePc
        first.length := by
    simp [Configuration.resumeAt, Configuration.rebasePc,
      Configuration.swapTapes, rewindBitstringStart, hOutput1,
      first, firstReturn, Program.asSubroutine_length,
      bits, List.map_replicate]
  let afterRewind : Configuration :=
    { pc := 7, inputTape := afterWidth.inputTape,
      outputTape :=
        ((rewindBitstringFinish bits afterWidth.inputTape).swapTapes).outputTape.moveRight.moveRight,
      halted := true }
  obtain ⟨v2, hv2, embedded2⟩ := rewindRun.withSubroutine_halted
    first OutputColumnRewind.toThird [.halt] finalReturn
    (Nat.zero_le _) rfl rfl
  have r2 : RunsFor program (afterWidth.resumeAt firstReturn)
      (afterRewind.resumeAt finalReturn) v2 := by
    rw [hJoin]
    simpa [second_layout, afterRewind] using embedded2
  have hFinal : Step program (afterRewind.resumeAt finalReturn)
      { afterRewind.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ afterRewind.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, width, rest, before, ?_,
    (r1.trans r2).succ hFinal, rfl, ?_, ?_, hw, hRest⟩
  · dsimp [bits] at hu2
    simp only [List.length_replicate] at hu2
    omega
  · simpa [afterRewind, Configuration.resumeAt] using hInput1
  · simpa [afterRewind, Configuration.resumeAt] using hOutput2

end Machine.FramedColumnPreparation
