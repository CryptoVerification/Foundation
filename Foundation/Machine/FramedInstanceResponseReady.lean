import Foundation.Machine.FramedInstanceResponsePrefix
import Foundation.Machine.BitstringRewind
import Foundation.Machine.TapeSwap

namespace Machine.FramedInstanceResponseReady

private def firstReturn : Nat := FramedInstanceResponsePrefix.program.length + 1
private def finalReturn : Nat := firstReturn + rewindBitstring.length + 1

/-- The response body remains unread. The copied instance code is rewound
by actual head moves so a following width checker can use its cells. -/
def program : Program :=
  FramedInstanceResponsePrefix.program.asSubroutine 0 firstReturn ++
    rewindBitstring.swapTapes.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceResponsePrefix.program
      (rewindBitstring.swapTapes.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (FramedInstanceResponsePrefix.program.asSubroutine 0 firstReturn)
      rewindBitstring.swapTapes [.halt] finalReturn := by
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

def budget (length : Nat) : Nat := 10000 * (length + 1) + 10000

/-- The first response bit stays under the input head. The output head is at
the first instance-code cell (or blank if the code is empty); an extra
physical blank at the far right is retained. -/
theorem runs_valid (n : Nat) (instanceBits reply : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.inputTape =
        { Tape.ofBits reply with
          left := some false :: List.replicate reply.length (some true) ++
            instanceBits.reverse.map some ++
              some false :: List.replicate instanceBits.length (some true) ++
                some false :: List.replicate n (some true) } ∧
      finish.outputTape =
        ({ right := instanceBits.map some ++ [none] } : Tape).moveRight := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨after, used₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedInstanceResponsePrefix.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponsePrefix.program
      (rewindBitstring.swapTapes.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded₁
  have rew := (rewindScratch_runs [] instanceBits after.inputTape).swapTapes
  have hJoin : after.resumeAt firstReturn =
      ((rewindScratchStart [] instanceBits after.inputTape).swapTapes).rebasePc
        firstReturn := by
    dsimp [Configuration.resumeAt, Configuration.rebasePc,
      Configuration.swapTapes, rewindScratchStart]
    rw [hOutput₁]
    rfl
  rw [hJoin] at firstRun
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    rew.withSubroutine_halted
      (FramedInstanceResponsePrefix.program.asSubroutine 0 firstReturn)
      rewindBitstring.swapTapes [.halt] finalReturn
      (by change 0 ≤ 4; omega) rfl rfl
  have secondRun : RunsFor program
      (((rewindScratchStart [] instanceBits after.inputTape).swapTapes).rebasePc
        firstReturn)
      (((rewindScratchFinish [] instanceBits after.inputTape).swapTapes).resumeAt
        finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  let tail := (rewindScratchFinish [] instanceBits after.inputTape).swapTapes
  refine ⟨{ tail.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, (firstRun.trans secondRun).succ (final_step tail),
    rfl, ?_, ?_⟩
  · simpa [tail, rewindScratchFinish, Configuration.resumeAt,
      Configuration.swapTapes] using hInput₁
  · simp [tail, rewindScratchFinish, Configuration.resumeAt,
      Configuration.swapTapes]

/-- The native rewind always stops at a blank to the left, even if a
malformed earlier frame left unexpected data on either tape. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    FramedInstanceResponsePrefix.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceResponsePrefix.program
      (rewindBitstring.swapTapes.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂, _⟩ :=
    rewindBitstring_terminates_from after.outputTape after.inputTape
  have swapped := run₂.swapTapes
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    swapped.withSubroutine_halted
      (FramedInstanceResponsePrefix.program.asSubroutine 0 firstReturn)
      rewindBitstring.swapTapes [.halt] finalReturn
      (by change 0 ≤ 4; omega) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.swapTapes.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc,
      Configuration.swapTapes] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : Machine.GuardedCompiler.sourceStorage
      (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;>
      simp [Machine.GuardedCompiler.sourceStorage, Configuration.initial,
        Tape.cells, Tape.ofBits] <;> omega
  have hCells : after.outputTape.left.length ≤ raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage, Tape.cells] at hStorage hInitial
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, FramedInstanceResponsePrefix.budget] at *
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstRun.trans secondRun).succ (final_step finish.swapTapes), rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact ((PolynomiallyBounded.const 10000).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 10000)

end Machine.FramedInstanceResponseReady
