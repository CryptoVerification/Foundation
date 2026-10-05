import Foundation.Crypto.Semantics.Machine.FramedInstanceResponseReady
import Foundation.Crypto.Semantics.Machine.ChooseFirstWidthCheck
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChooseFirstWidthPrefix

private def firstReturn : Nat := FramedInstanceResponseReady.program.length + 1
private def finalReturn : Nat := firstReturn + ChooseFirstWidthCheck.program.length + 1

/-- One fixed program copies and rewinds the instance code, reads the
response frame, checks the choose tag, and tests the first element width.
The remaining validity tests and output reconstruction are separate work. -/
def program : Program :=
  FramedInstanceResponseReady.program.asSubroutine 0 firstReturn ++
    ChooseFirstWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceResponseReady.program
      (ChooseFirstWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseFirstWidthCheck.program [.halt] finalReturn := by
  simp [program, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalReturn)
      { c.resumeAt finalReturn with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by native_decide
  simp [Step, successors, next, Configuration.resumeAt, hLookup,
    Instruction.next]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat := 200000 * (length + 1) + 200000

/-- On a correctly framed response with a choose tag, the status cell is
true exactly when the first element field has the width advertised by the
three-field instance code. The rest of the reply is not consumed by magic. -/
theorem runs_width_status (n width : Nat) (instanceBits field tail : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: FiniteBitEncoding.delimit field ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current = some (decide (field.length = width)) := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit field ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨after, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedInstanceResponseReady.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseFirstWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  let expected := ChooseFirstWidthCheck.start before [none] instanceBits reply
  have hEquivalent : (expected.rebasePc firstReturn).Equivalent
      (after.resumeAt firstReturn) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected, ChooseFirstWidthCheck.start, before,
        Configuration.rebasePc, Configuration.resumeAt, hInput₁] using
        (Tape.Equivalent.refl ({ Tape.ofBits reply with left := before } : Tape))
    · have hRew := rewindScratchFinish_input_equivalent [] instanceBits after.inputTape
      simpa [expected, ChooseFirstWidthCheck.start,
        Configuration.rebasePc, Configuration.resumeAt, hOutput₁,
        rewindScratchFinish] using hRew.symm
  obtain ⟨finish, used₂, _hUsed₂, checkRun, hHalt₂, hStatus⟩ :=
    ChooseFirstWidthCheck.runs_width_status before [none] width
      instanceBits field tail hLength
  have hExpected : expected = ChooseFirstWidthCheck.start before [none]
      instanceBits (false :: FiniteBitEncoding.delimit field ++ tail) := rfl
  rw [← hExpected] at checkRun
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    checkRun.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseFirstWidthCheck.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have checkEmbedded : RunsFor program (expected.rebasePc firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    checkEmbedded.exists_equivalent hEquivalent
  have hActualPc : actual.pc = finalReturn := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActualHalt : actual.halted = false := by
    exact hActual.2.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalReturn]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  refine ⟨{ actual with halted := true }, returned₁ + returned₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_⟩
  exact (hActual.2.2.2.1.symm).trans (by
    simpa [Configuration.resumeAt] using hStatus)

/-- The connected prefix stops on all finite inputs, including malformed
outer frames, wrong-stage tags, and truncated first element delimiters. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    FramedInstanceResponseReady.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponseReady.program
      (ChooseFirstWidthCheck.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseFirstWidthCheck.terminates_from_anyTape
      after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedInstanceResponseReady.program.asSubroutine 0 firstReturn)
      ChooseFirstWidthCheck.program [.halt] finalReturn
      (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : Machine.GuardedCompiler.sourceStorage
      (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;>
      simp [Machine.GuardedCompiler.sourceStorage, Configuration.initial,
        Tape.cells, Tape.ofBits] <;> omega
  have hCells : after.inputTape.right.length ≤ raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage, Tape.cells] at hStorage hInitial
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, FramedInstanceResponseReady.budget] at *
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstRun.trans secondRun).succ (final_step finish), rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

/-- The common all-input polynomial budget observes the same width status
as the exact native trace, even if the trace stops before that budget. -/
theorem eval_width_status (n width : Nat) (instanceBits field tail : List Bool)
    (hLength : instanceBits.length = 3 * width) :
    let reply := false :: FiniteBitEncoding.delimit field ++ tail
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    (evalConfigWithin program (Configuration.initial raw)
      (budget raw.length)).map (fun c => c.outputTape.current) =
      PMF.pure (some (decide (field.length = width))) := by
  dsimp only
  let reply := false :: FiniteBitEncoding.delimit field ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨finish, used, run, hHalt, hStatus⟩ :=
    runs_width_status n width instanceBits field tail hLength
  have hAtUsed : HaltsWithin program raw used :=
    run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  have hAtBudget := haltsWithin raw
  let common := max used (budget raw.length)
  have hUsedStable : evalConfigWithin program (Configuration.initial raw) common =
      evalConfigWithin program (Configuration.initial raw) used := by
    have h := evalConfigWithin_stable program raw used (common - used) hAtUsed
    simpa [common, Nat.add_sub_of_le (le_max_left used (budget raw.length))] using h
  have hBudgetStable : evalConfigWithin program (Configuration.initial raw) common =
      evalConfigWithin program (Configuration.initial raw)
        (budget raw.length) := by
    have h := evalConfigWithin_stable program raw (budget raw.length)
      (common - budget raw.length) hAtBudget
    simpa [common, Nat.add_sub_of_le (le_max_right used (budget raw.length))] using h
  rw [← hBudgetStable, hUsedStable,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hStatus]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact ((PolynomiallyBounded.const 200000).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 200000)

end Machine.ChooseFirstWidthPrefix
