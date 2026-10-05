import Foundation.Crypto.Semantics.Machine.ChooseResponsePrefix
import Foundation.Crypto.Semantics.Machine.ChooseTwoFields
import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Foundation.Crypto.Semantics.Machine.MessageSelectionPreparation

namespace Machine.ChooseResponseParser

private def firstReturn : Nat := ChooseResponsePrefix.program.length + 1
private def finalReturn : Nat := firstReturn + ChooseTwoFields.program.length + 1

/-- One fixed finite program joins the outer framed-request scan with the
two inner delimited-field scans. It only parses: range and subgroup tests,
fallback construction, and state-preserving reply construction remain later
stages of the choose normalizer. -/
def program : Program :=
  ChooseResponsePrefix.program.asSubroutine 0 firstReturn ++
    ChooseTwoFields.program.asSubroutine firstReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] ChooseResponsePrefix.program
      (ChooseTwoFields.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, Program.withSubroutine]

private theorem second_layout : program =
    Program.withSubroutine
      (ChooseResponsePrefix.program.asSubroutine 0 firstReturn)
      ChooseTwoFields.program [.halt] finalReturn := by
  simp [program, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration) :
    Step program (c.resumeAt finalReturn)
      { c.resumeAt finalReturn with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by native_decide
  exact Step.resumeAt_halt c finalReturn hLookup

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

def budget (length : Nat) : Nat := 50000 * (length + 1) + 50000

/-- The outer frame parser and both inner delimiter parsers jointly stop on
every finite request, including malformed frames and wrong-stage replies. -/
theorem runs_any (raw : List Bool) :
    ∃ finish used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨after, used₁, hUsed₁, run₁, hHalt₁⟩ :=
    ChooseResponsePrefix.runs_any raw
  obtain ⟨returned₁, hReturned₁, embedded₁⟩ :=
    run₁.withSubroutine_halted [] ChooseResponsePrefix.program
      (ChooseTwoFields.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨finish, used₂, hUsed₂, run₂, hHalt₂⟩ :=
    ChooseTwoFields.terminates_from_anyTape after.inputTape after.outputTape
  obtain ⟨returned₂, hReturned₂, embedded₂⟩ :=
    run₂.withSubroutine_halted
      (ChooseResponsePrefix.program.asSubroutine 0 firstReturn)
      ChooseTwoFields.program [.halt] finalReturn
      (by change 0 ≤ 41; omega) rfl hHalt₂
  have secondRun : RunsFor program (after.resumeAt firstReturn)
      (finish.resumeAt finalReturn) returned₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  have hStorage := Machine.GuardedCompiler.sourceStorage_le_of_initial_run run₁
  have hCells : after.inputTape.cells + after.outputTape.cells ≤
      raw.length + 2 + used₁ := hStorage
  have hBound : returned₁ + returned₂ + 1 ≤ budget raw.length := by
    dsimp only [budget, ChooseResponsePrefix.budget] at *
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
  exact ((PolynomiallyBounded.const 50000).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 50000)

/-- On the exact request framing and canonical choose-response shape, the
physical parser returns both message payloads with explicit success bits.
The reply state is retained on the input tape. -/
theorem runs_canonical (n : Nat) (instanceBits first second state : List Bool) :
    let reply := canonicalMessageBits first second state
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ finish used,
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputBits = first ++ [true] ++ second ++ [true] := by
  dsimp only
  let reply := canonicalMessageBits first second state
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let before : List (Option Bool) :=
    some false :: List.replicate reply.length (some true) ++
      instanceBits.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  obtain ⟨after, used₁, prefixRun, hHalt₁, hInput₁, hOutput₁⟩ :=
    ChooseResponsePrefix.runs_valid n instanceBits reply
  obtain ⟨returned₁, _hReturned₁, embedded₁⟩ :=
    prefixRun.withSubroutine_halted [] ChooseResponsePrefix.program
      (ChooseTwoFields.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn (Nat.zero_le _) rfl hHalt₁
  have firstRun : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) returned₁ := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded₁
  let expected : Configuration :=
    { inputTape := { Tape.ofBits reply with left := before } }
  have hEquivalent : (expected.rebasePc firstReturn).Equivalent
      (after.resumeAt firstReturn) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [expected, Configuration.rebasePc, Configuration.resumeAt,
        before, hInput₁] using
        (Tape.Equivalent.refl ({ Tape.ofBits reply with left := before } : Tape))
    · simpa [expected, Configuration.rebasePc, Configuration.resumeAt] using
        hOutput₁.symm
  let innerBefore : List (Option Bool) :=
    (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: before
  let innerOutput : List (Option Bool) := some true :: first.reverse.map some
  let secondFinish : Configuration :=
    { (readDelimitedContextFinish innerBefore innerOutput second
        (state.map some)).resumeAt 40 with halted := true }
  obtain ⟨used₂, _hUsed₂, secondRun⟩ :=
    ChooseTwoFields.runs_canonical_from before first second state
  have hReply : reply = false ::
      (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ state) := by
    rfl
  have hStart : expected =
      ({ inputTape := { Tape.ofBits
          (false :: (FiniteBitEncoding.delimit first ++
            FiniteBitEncoding.delimit second ++ state)) with left := before } } :
        Configuration) := by
    simp [expected, hReply]
  rw [← hStart] at secondRun
  obtain ⟨embeddedUsed₂, _hEmbeddedUsed₂, embedded₂⟩ :=
    secondRun.withSubroutine_halted
      (ChooseResponsePrefix.program.asSubroutine 0 firstReturn)
      ChooseTwoFields.program [.halt] finalReturn
      (by change 0 ≤ 41; omega) rfl rfl
  have secondRun' : RunsFor program
      (expected.rebasePc firstReturn)
      (secondFinish.resumeAt finalReturn) embeddedUsed₂ := by
    simpa [second_layout, firstReturn, Program.asSubroutine_length,
      secondFinish, innerBefore, innerOutput] using embedded₂
  obtain ⟨actual, actualRun, hActual⟩ :=
    secondRun'.exists_equivalent hEquivalent
  have hActualHalt : actual.halted = false := by
    exact hActual.2.1.symm
  have hActualPc : actual.pc = finalReturn := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hLast : Step program actual { actual with halted := true } := by
    have hLookup : program[finalReturn]? = some .halt := by native_decide
    simp [Step, successors, next, hActualPc, hActualHalt,
      hLookup, Instruction.next]
  let target : Configuration := { actual with halted := true }
  refine ⟨target, returned₁ + embeddedUsed₂ + 1,
    (firstRun.trans actualRun).succ hLast, rfl, ?_⟩
  have hOutput := hActual.outputBits
  have hSecondOutput : secondFinish.outputBits =
      first ++ [true] ++ second ++ [true] := by
    change (readDelimitedContextFinish innerBefore innerOutput second
      (state.map some)).outputBits = _
    exact ChooseTwoFields.canonical_output first second state
  change actual.outputBits = _
  exact hOutput.symm.trans hSecondOutput

/-- Exact evaluator law for the framed two-field parser. The result is still
the staging payload/status representation, not a normalized response. -/
theorem eval_canonical (n : Nat) (instanceBits first second state : List Bool) :
    let reply := canonicalMessageBits first second state
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (first ++ [true] ++ second ++ [true])) := by
  dsimp only
  let reply := canonicalMessageBits first second state
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨finish, used, run, hHalt, hOutput⟩ :=
    runs_canonical n instanceBits first second state
  have hHaltsWith : HaltsWith program raw
      (first ++ [true] ++ second ++ [true]) used :=
    ⟨_, run, hHalt, hOutput⟩
  rw [evalWithin_eq_of_haltsWithin program raw (budget raw.length) used
    (haltsWithin raw) (hHaltsWith.haltsWithin_of_no_randomBit no_randomBit)]
  exact hHaltsWith.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.ChooseResponseParser
