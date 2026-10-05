import Foundation.Crypto.Semantics.Machine.FramedArithmeticPrefix
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.ChooseResponsePrefix

private def firstReturn : Nat := FramedArithmeticPrefix.program.length + 1
private def finalReturn : Nat := firstReturn + skipUnary.length + 1

/-- Consume the security-parameter encoding, the instance frame, and the
response frame's unary length header. On a valid input, the head reaches the
first bit of the raw choose response. Neither the instance nor response is
decoded by a free operation. -/
def program : Program :=
  FramedArithmeticPrefix.program.asSubroutine 0 firstReturn ++
    skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedArithmeticPrefix.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (FramedArithmeticPrefix.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn := by
  simp [program, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalReturn)
      { c.resumeAt finalReturn with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    native_decide
  exact Step.resumeAt_halt c finalReturn hLookup

/-- Native layout theorem on the exact request shape expected by the
represented normalizer. The arbitrary response body itself is retained. -/
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
      finish.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let saved : List (Option Bool) :=
    instanceBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
  obtain ⟨after, used₁, _hUsed₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedArithmeticPrefix.runs_valid n instanceBits (frame reply)
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedArithmeticPrefix.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn
      (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  have hStart : after.resumeAt firstReturn =
      (skipUnaryStart saved reply.length reply after.outputTape).rebasePc firstReturn := by
    simp [Configuration.resumeAt, Configuration.rebasePc,
      skipUnaryStart, hInput₁, saved, frame,
      encodeSecurityParameter, List.append_assoc]
  rw [hStart] at firstRun
  have run₂ := skipUnary_runs saved reply.length reply after.outputTape
  obtain ⟨returned₂, _hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedArithmeticPrefix.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn (Nat.zero_le _) rfl rfl
  have secondRun : RunsFor program
      ((skipUnaryStart saved reply.length reply after.outputTape).rebasePc firstReturn)
      ((skipUnaryFinish saved reply.length reply after.outputTape).resumeAt finalReturn)
      returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length] using embedded₂
  let tail := skipUnaryFinish saved reply.length reply after.outputTape
  refine ⟨{ tail.resumeAt finalReturn with halted := true },
    returned₁ + returned₂ + 1, (firstRun.trans secondRun).succ (final_step tail),
    rfl, ?_, ?_⟩
  · simp [tail, skipUnaryFinish, saved, Configuration.resumeAt,
      List.append_assoc]
  · simpa [tail, skipUnaryFinish, Configuration.resumeAt] using hOutput₁

def budget (length : Nat) : Nat := 100 * (length + 1) + 100

/-- The outer parser also stops on every malformed finite request. The
retained instance bytes are never interpreted as an oracle instruction. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    FramedArithmeticPrefix.runs raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] FramedArithmeticPrefix.program
      (skipUnary.asSubroutine firstReturn finalReturn ++ [.halt]) firstReturn
      (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂, _hOutput₂⟩ :=
    skipUnary_terminates_from_anyTape after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (FramedArithmeticPrefix.program.asSubroutine 0 firstReturn)
      skipUnary [.halt] finalReturn (Nat.zero_le _) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_initial_run run₁
  have hCells : after.inputTape.cells ≤ raw.length + 2 + used₁ := by
    dsimp only [Machine.GuardedCompiler.sourceStorage] at hStorage
    omega
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, FramedArithmeticPrefix.budget] at *
    omega
  have run : RunsFor program (Configuration.initial raw)
      { finish.resumeAt finalReturn with halted := true }
      (returned₁ + returned₂ + 1) :=
    (firstRun.trans secondRun).succ (final_step finish)
  exact ⟨_, returned₁ + returned₂ + 1, hBound, run, rfl⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHaltsWith : HaltsWith program raw finish.outputBits used :=
    ⟨_, run, hHalt, rfl⟩
  exact (hHaltsWith.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact ((PolynomiallyBounded.const 100).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 100)

end Machine.ChooseResponsePrefix
