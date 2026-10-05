import Foundation.Crypto.Semantics.Machine.BinaryPowerExternalWidth
import Foundation.Crypto.Semantics.Machine.OutputIsOne
import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine.BinaryPowerIsOne

private theorem getD_append_none (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- Erasing the final padded power bit leaves a contiguous output block
followed only by blank padding, also on malformed raw inputs. -/
private theorem stripped_block (rawOutput : List Bool) (blanks : Nat) :
    ∃ bits : List Bool,
      (({ left := rawOutput.reverse.map some ++ [none],
           right := List.replicate blanks none } : Tape).moveLeft.write none).Equivalent
        { left := bits.reverse.map some } ∧
      bits.length ≤ rawOutput.length := by
  cases hReverse : rawOutput.reverse with
  | nil =>
      refine ⟨[], ?_, by simp⟩
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        simp [Tape.moveLeft, Tape.write]
      · intro i
        cases i with
        | zero => simp [Tape.moveLeft, Tape.write]
        | succ i =>
            simp [Tape.moveLeft, Tape.write]
  | cons bit rest =>
      refine ⟨rest.reverse, ?_, ?_⟩
      · refine ⟨rfl, ?_, ?_⟩
        · intro i
          simpa [Tape.moveLeft, Tape.write, List.map_cons] using
            getD_append_none (rest.map some) i
        · intro i
          cases i with
          | zero => simp [Tape.moveLeft, Tape.write, List.map_cons]
          | succ i =>
              simp [Tape.moveLeft, Tape.write, List.map_cons]
      · have hLength := congrArg List.length hReverse
        simp at hLength ⊢
        omega

private def powerReturn (core : Program) : Nat := core.length + 1
private def checkReturn (core : Program) : Nat :=
  powerReturn core + OutputIsOne.program.length + 1
private def beforeCheck (core : Program) : Program :=
  core.asSubroutine 0 (powerReturn core)

/-- The modular-power evaluator and the in-place output test are invoked
on the same physical tapes. No mathematical intermediate bitstring is loaded
as a fresh machine input. -/
def withCore (core : Program) : Program :=
  beforeCheck core ++
    OutputIsOne.program.asSubroutine (powerReturn core) (checkReturn core) ++ [.halt]

def program : Program := withCore BinaryPowerExternalWidth.program

private theorem withCore_no_randomBit (core : Program)
    (hCore : ∀ tape, Instruction.randomBit tape ∉ core)
    (tape : TapeId) :
    Instruction.randomBit tape ∉ withCore core := by
  have hFirst := Program.asSubroutine_no_randomBit core hCore
    0 (powerReturn core) tape
  have hSecond := Program.asSubroutine_no_randomBit OutputIsOne.program
    OutputIsOne.no_randomBit (powerReturn core) (checkReturn core) tape
  simp only [withCore, beforeCheck, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or]
  exact ⟨⟨hFirst, hSecond⟩, by simp⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program :=
  withCore_no_randomBit _ BinaryPowerExternalWidth.no_randomBit tape

private theorem beforeCheck_length (core : Program) :
    (beforeCheck core).length = powerReturn core := by
  exact Program.asSubroutine_length _ _ _

private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] core
      (OutputIsOne.program.asSubroutine (powerReturn core) (checkReturn core) ++ [.halt])
      (powerReturn core) := by
  simp only [withCore, beforeCheck, Program.withSubroutine,
    List.length_nil, List.nil_append, List.append_assoc]

private theorem second_layout (core : Program) : withCore core =
    Program.withSubroutine (beforeCheck core) OutputIsOne.program [.halt]
      (checkReturn core) := by
  simp only [withCore, Program.withSubroutine, beforeCheck_length]

def budget (length : Nat) : Nat :=
  BinaryPowerExternalWidth.budget length +
    OutputIsOne.budget (BinaryPowerExternalWidth.budget length + 1) + 3

/-- Longer arithmetic inputs can use the same explicit stopping budget. -/
theorem budget_monotone : Monotone budget := by
  intro a b h
  unfold budget BinaryPowerExternalWidth.budget OutputIsOne.budget
    BinaryPowerPadded.budget BinaryWorkspacePreparation.budget BinaryPowerProgram.budget
  gcongr

theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  have hPower : PolynomiallyBounded BinaryPowerExternalWidth.budget :=
    BinaryPowerPadded.budget_polynomiallyBounded.add
      (PolynomiallyBounded.const 4)
  have hCheck : PolynomiallyBounded
      (fun n => OutputIsOne.budget (BinaryPowerExternalWidth.budget n + 1)) :=
    ((PolynomiallyBounded.const 8).mul
      ((hPower.add (PolynomiallyBounded.const 1)).add
        (PolynomiallyBounded.const 1))).add
          (PolynomiallyBounded.const 10)
  exact (hPower.add
    hCheck).add (PolynomiallyBounded.const 3)

private theorem halt_lookup (core : Program) :
    (withCore core)[checkReturn core]? = some .halt := by
  rw [second_layout core]
  have hIndex : checkReturn core = (beforeCheck core).length +
      OutputIsOne.program.length + 1 + 0 := by
    simp only [checkReturn, beforeCheck_length, Nat.add_zero]
  rw [hIndex, Program.withSubroutine_getElem?_suffix]
  rfl

private theorem halt_step (core : Program) (c : Configuration) :
    Step (withCore core) (c.resumeAt (checkReturn core))
      { c.resumeAt (checkReturn core) with halted := true } := by
  simp [Step, successors, next, halt_lookup core,
    Configuration.resumeAt, Instruction.next]

/-- Composition is proved with the first code abstract, so Lean never needs
to normalize the very large concrete power instruction list while checking
the subroutine address arithmetic. -/
private theorem runs_withCore (core : Program) (coreBudget : Nat → Nat)
    (raw : List Bool)
    (hCore : ∃ (rawOutput : List Bool) (powerTarget : Configuration)
      (powerUsed blanks : Nat),
      powerUsed ≤ coreBudget raw.length ∧
      RunsFor core (Configuration.initial raw) powerTarget powerUsed ∧
      powerTarget.halted = true ∧
      powerTarget.outputTape.Equivalent
        (({ left := rawOutput.reverse.map some ++ [none],
             right := List.replicate blanks none } : Tape).moveLeft.write none)) :
    ∃ (powerTarget : Configuration) (powerUsed : Nat) (bits : List Bool)
      (finish : Configuration) (used : Nat),
      used ≤ coreBudget raw.length +
        OutputIsOne.budget (coreBudget raw.length + 1) + 3 ∧
      powerUsed ≤ coreBudget raw.length ∧
      RunsFor core (Configuration.initial raw) powerTarget powerUsed ∧
      powerTarget.halted = true ∧
      RunsFor (withCore core) (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      powerTarget.outputBits = bits ∧
      finish.outputBits = [BinaryIsOneInPlace.accepts bits] := by
  obtain ⟨rawOutput, powerTarget, powerUsed, blanks,
    hPowerUsed, powerRun, hPowerHalt, hPowerLayout⟩ := hCore
  obtain ⟨bits, hBlock, _⟩ := stripped_block rawOutput blanks
  have hPowerBlock : powerTarget.outputTape.Equivalent
      { left := bits.reverse.map some } := hPowerLayout.trans hBlock
  have hPowerBits : powerTarget.outputBits = bits := by
    have hBits := hPowerBlock.bits
    simpa [Configuration.outputBits, Tape.bits] using hBits
  have hBitsBound : bits.length ≤
      coreBudget raw.length + 1 := by
    have hStorage := outputBits_length_le_of_paddedRun
      core raw powerRun.toPadded
    rw [hPowerBits] at hStorage
    omega
  obtain ⟨checked, checkUsed, hCheckUsed, checkRun, hCheckHalt,
    hCheckBits⟩ := OutputIsOne.runs_from_block bits
      powerTarget.inputTape powerTarget.outputTape hPowerBlock
  obtain ⟨firstUsed, hFirstUsed, embeddedFirst⟩ :=
    powerRun.withSubroutine_halted [] core
      (OutputIsOne.program.asSubroutine (powerReturn core) (checkReturn core) ++ [.halt])
      (powerReturn core) (Nat.zero_le _) rfl hPowerHalt
  have firstRun : RunsFor (withCore core) (Configuration.initial raw)
      (powerTarget.resumeAt (powerReturn core)) firstUsed := by
    rw [first_layout core]
    simpa [Configuration.rebasePc] using embeddedFirst
  obtain ⟨secondUsed, hSecondUsed, embeddedSecond⟩ :=
    checkRun.withSubroutine_halted (beforeCheck core) OutputIsOne.program
      [.halt] (checkReturn core) (Nat.zero_le _) rfl hCheckHalt
  have secondRun : RunsFor (withCore core)
      (powerTarget.resumeAt (powerReturn core))
      (checked.resumeAt (checkReturn core)) secondUsed := by
    rw [second_layout core]
    simpa [beforeCheck_length core, Configuration.resumeAt,
      Configuration.rebasePc] using embeddedSecond
  let final : Configuration :=
    { checked.resumeAt (checkReturn core) with halted := true }
  refine ⟨powerTarget, powerUsed, bits, final, firstUsed + secondUsed + 1,
    ?_, hPowerUsed, powerRun, hPowerHalt,
    (firstRun.trans secondRun).succ (halt_step core checked), rfl,
    hPowerBits, hCheckBits⟩
  dsimp [OutputIsOne.budget] at *
  omega

/-- Every raw input halts. The returned bit tests the exact bitstring left
by the native power computation after its charged high-bit erasure. -/
theorem runs_any (raw : List Bool) :
    ∃ (powerTarget : Configuration) (powerUsed : Nat) (bits : List Bool)
      (finish : Configuration) (used : Nat),
      used ≤ budget raw.length ∧
      powerUsed ≤ BinaryPowerExternalWidth.budget raw.length ∧
      RunsFor BinaryPowerExternalWidth.program
        (Configuration.initial raw) powerTarget powerUsed ∧
      powerTarget.halted = true ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      powerTarget.outputBits = bits ∧
      finish.outputBits = [BinaryIsOneInPlace.accepts bits] := by
  obtain ⟨rawOutput, target, used, blanks, hUsed, run,
    hHalted, hLayout, _⟩ := BinaryPowerExternalWidth.runs raw
  exact runs_withCore BinaryPowerExternalWidth.program
    BinaryPowerExternalWidth.budget raw
      ⟨rawOutput, target, used, blanks, hUsed, run, hHalted, hLayout⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨_, _, _, finish, used, hUsed, _, _, _, run, hHalt, _⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

/-- On a valid assembled arithmetic triple, the *connected* finite program
returns whether the modular power is numerically one. Its output-check stage
reads and erases the actual power output tape. -/
theorem eval_numbers (width modulus first exponent : Nat)
    (hOne : 1 < modulus) (hFirst : first < modulus)
    (hExponent : exponent < 2 ^ width)
    (hModulus : modulus < 2 ^ width) :
    let raw := BinaryModularAddition.interleave
      (BinaryProductExternalWidth.numberColumns width modulus first exponent)
    evalWithin program raw (budget raw.length) =
      PMF.pure (some [BinaryIsOneInPlace.accepts
        (Binary.encode width (first ^ exponent % modulus))]) := by
  dsimp only
  let raw := BinaryModularAddition.interleave
    (BinaryProductExternalWidth.numberColumns width modulus first exponent)
  obtain ⟨powerTarget, powerUsed, bits, finish, used,
    hUsed, hPowerUsed, powerRun, hPowerHalt, run, hHalt,
    hPowerBits, hFinishBits⟩ := runs_any raw
  have hPowerAll := powerRun.haltsFrom_of_no_randomBit hPowerHalt
    BinaryPowerExternalWidth.no_randomBit (Nat.le_refl powerUsed)
  have hPowerEval : evalWithin BinaryPowerExternalWidth.program raw
      (BinaryPowerExternalWidth.budget raw.length) =
      PMF.pure (some bits) := by
    unfold evalWithin
    rw [evalConfigWithin_eq_of_le _ _ _ _ hPowerUsed hPowerAll,
      powerRun.evalConfigWithin_eq_pure_of_no_randomBit
        BinaryPowerExternalWidth.no_randomBit]
    simp [PMF.pure_map, hPowerHalt, hPowerBits]
  have hExpected := BinaryPowerExternalWidth.eval_numbers width modulus
    first exponent hOne hFirst hExponent hModulus
  change evalWithin BinaryPowerExternalWidth.program raw
    (BinaryPowerExternalWidth.budget raw.length) =
      PMF.pure (some (Binary.encode width (first ^ exponent % modulus)))
    at hExpected
  have hEqPure : PMF.pure (some bits) =
      PMF.pure (some (Binary.encode width (first ^ exponent % modulus))) :=
    hPowerEval.symm.trans hExpected
  have hMem : some bits ∈
      (PMF.pure (some (Binary.encode width
        (first ^ exponent % modulus)))).support := by
    rw [← hEqPure]
    simp
  have hBits : bits = Binary.encode width
      (first ^ exponent % modulus) := by
    simpa using hMem
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hFinishBits, hBits]

/-- Invoke the subgroup test through the native guarded interpreter on the
opposite tape. Both saved caller prefixes survive; the arithmetic input is
consumed by real transitions of the fixed compiled code. -/
theorem guarded_eval_numbers (width modulus first exponent : Nat)
    (hOne : 1 < modulus) (hFirst : first < modulus)
    (hExponent : exponent < 2 ^ width) (hModulus : modulus < 2 ^ width)
    (beforeColumns beforeReply : List (Option Bool)) :
    let raw := BinaryModularAddition.interleave
      (BinaryProductExternalWidth.numberColumns width modulus first exponent)
    ∃ c : Configuration, c.halted = true ∧
      c.outputBits = [BinaryIsOneInPlace.accepts
        (Binary.encode width (first ^ exponent % modulus))] ∧
      evalConfigWithin (GuardedCompiler.rawCompileOpposite program)
        (GuardedCompiler.packInputStart beforeColumns beforeReply raw).swapTapes
        (GuardedCompiler.rawTraceBudget budget raw.length) =
          PMF.pure (GuardedCompiler.rawResultFrom program raw
            beforeColumns beforeReply c).swapTapes := by
  dsimp only
  exact GuardedCompiler.rawCompileOpposite_result program _ _
    beforeColumns beforeReply budget no_randomBit (haltsWithin _)
    (eval_numbers width modulus first exponent hOne hFirst hExponent hModulus)

end Machine.BinaryPowerIsOne
