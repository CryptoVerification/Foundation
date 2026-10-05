import Foundation.Crypto.Semantics.Machine.FramedInstanceCopy
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedInstanceResponsePrefix

private def firstReturn : Nat := FramedInstanceCopy.program.length + 1
private def finalReturn : Nat := firstReturn + skipUnary.length + 1

/-- Copy the complete instance code to the output tape and consume the
response frame's unary header. The instance bits remain a physical width
counter for subsequent native validation of the response fields. -/
def program : Program :=
  FramedInstanceCopy.program.asSubroutine 0 firstReturn ++
    skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceCopy.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (FramedInstanceCopy.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn := by
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

def budget (length : Nat) : Nat := 1000 * (length + 1) + 1000

/-- The response body is left unread while the complete instance code is
retained on the output tape, separated from preceding data by a blank. -/
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
        { left := instanceBits.reverse.map some ++ [none] } := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨after, used₁, _hUsed₁, run₁, hHalt₁, hInput₁, hOutput₁, _⟩ :=
    FramedInstanceCopy.runs_valid n instanceBits (frame reply)
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceCopy.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program
      (Configuration.initial raw) (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw, List.append_assoc] using embedded₁
  let saved : List (Option Bool) :=
    instanceBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
  let output : Tape := { left := instanceBits.reverse.map some ++ [none] }
  have hJoin : after.resumeAt firstReturn =
      (skipUnaryStart saved reply.length reply output).rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc, skipUnaryStart,
      hInput₁, hOutput₁, saved, output, frame, encodeSecurityParameter,
      List.append_assoc]
  rw [hJoin] at firstRun
  have second := skipUnary_runs saved reply.length reply output
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    second.withSubroutine_halted
      (FramedInstanceCopy.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn (Nat.zero_le _) rfl rfl
  have secondRun : RunsFor program
      ((skipUnaryStart saved reply.length reply output).rebasePc firstReturn)
      ((skipUnaryFinish saved reply.length reply output).resumeAt finalReturn)
      returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  let tail := skipUnaryFinish saved reply.length reply output
  refine ⟨{ tail.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, (firstRun.trans secondRun).succ (final_step tail),
    rfl, ?_, ?_⟩
  · simp [tail, skipUnaryFinish, saved, Configuration.resumeAt,
      List.append_assoc]
  · simp [tail, skipUnaryFinish, output, Configuration.resumeAt]

/-- Both native parsers stop on all finite inputs, including malformed
headers and truncated instance or response frames. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    FramedInstanceCopy.runs raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedInstanceCopy.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂, _⟩ :=
    skipUnary_terminates_from_anyTape after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedInstanceCopy.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
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
  have hCells : after.inputTape.cells ≤ raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage hInitial
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, FramedInstanceCopy.budget] at *
    omega
  exact ⟨_, returned₁ + returned₂ + 1, hBound,
    (firstRun.trans secondRun).succ (final_step finish), rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact ((PolynomiallyBounded.const 1000).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 1000)

end Machine.FramedInstanceResponsePrefix
