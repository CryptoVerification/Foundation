import Foundation.Machine.FramedColumnSlotFill
import Foundation.Machine.NativeInvocation

namespace Machine.InstanceExponentCopy

private def pre : Program := [.moveRight .output, .jump 7]
private def finalPc : Nat := 2 + FramedColumnSlotFill.program.length + 1

/-- Enter the existing slot writer at its payload loop, skipping no input
header. One output move selects the exponent track of the modulus template.
The instance exponent is fixed width and is not separately framed. -/
def program : Program :=
  Program.withSubroutine pre FramedColumnSlotFill.program [.halt] finalPc

private def entry (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before }, outputTape := output }

private def payload (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 5, inputTape := { Tape.ofBits bits with left := before }, outputTape := output.moveRight }

private theorem prefix_eval (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    evalConfigWithin program (entry before bits output) 2 =
      PMF.pure ((payload before bits output).rebasePc 2) := by
  simp [evalConfigWithin, stepPMF, next, program, pre, Program.withSubroutine,
    entry, payload, Configuration.rebasePc, Instruction.next, Configuration.advance,
    Configuration.updateTape, PMF.pure_bind]

private theorem wrap_run (before : List (Option Bool)) (bits : List Bool) (output : Tape)
    (target : Configuration) (used : Nat)
    (run : RunsFor FramedColumnSlotFill.program (payload before bits output) target used)
    (hHalt : target.halted = true) :
    ∃ consumed, consumed ≤ used + 3 ∧
      RunsFor program (entry before bits output)
        { target.resumeAt finalPc with halted := true } consumed := by
  have hSupport : ((payload before bits output).rebasePc 2) ∈
      (evalConfigWithin program (entry before bits output) 2).support := by
    rw [prefix_eval]
    simp
  obtain ⟨u, hu, prefixRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  obtain ⟨v, hv, embedded⟩ := run.withSubroutine_halted pre
    FramedColumnSlotFill.program [.halt] finalPc (by change 5 ≤ 17; decide) rfl hHalt
  have hSource : RunsFor program ((payload before bits output).rebasePc 2)
      (target.resumeAt finalPc) v := by simpa [program, pre] using embedded
  have hLookup : program[finalPc]? = some .halt := by
    change (Program.withSubroutine pre FramedColumnSlotFill.program [.halt] finalPc)[finalPc]? = _
    have hIndex : finalPc = pre.length + FramedColumnSlotFill.program.length + 1 + 0 := rfl
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  have hLast : Step program (target.resumeAt finalPc)
      { target.resumeAt finalPc with halted := true } := by
    simp [Step, successors, next, Configuration.resumeAt, hLookup, Instruction.next]
  exact ⟨u + v + 1, by omega, (prefixRun.trans hSource).succ hLast⟩

/-- The output column boundary limits the payload. Arbitrary malformed
finite input therefore terminates while retaining its unread suffix. -/
theorem runs_any (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    ∃ target remaining before' used,
      used ≤ 9 * bits.length + 6 ∧
      RunsFor program (entry before bits output) target used ∧ target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  obtain ⟨target, remaining, before', u, hu, run, hHalt, hInput, hLength⟩ :=
    FramedColumnSlotFill.runs_payload_any before bits output.moveRight
  change RunsFor FramedColumnSlotFill.program (payload before bits output) target u at run
  obtain ⟨used, hUsed, wrapped⟩ := wrap_run before bits output target u run hHalt
  exact ⟨{ target.resumeAt finalPc with halted := true }, remaining, before', used,
    by omega, wrapped, rfl, hInput, hLength⟩

/-- Copy the actual exponent bits from the instance into the second track,
leaving the generator and following response unexamined on the input tape. -/
theorem runs_exponent (exponent modulus tail : List Bool)
    (hExponent : exponent.length = modulus.length) (before : List (Option Bool)) :
    ∃ target used, used ≤ 9 * exponent.length + 5 ∧
      RunsFor program
        (entry before (exponent ++ tail) (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)))
        target used ∧ target.halted = true ∧
      target.inputTape = { Tape.ofBits tail with left := exponent.reverse.map some ++ before } ∧
      target.outputTape = { left := none ::
        (BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus).reverse.map some } := by
  let ideal : Configuration :=
    { pc := 16,
      inputTape := { Tape.ofBits tail with left := exponent.reverse.map some ++ before },
      outputTape := { left := none ::
        (BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus).reverse.map some },
      halted := true }
  have hCopy := FramedColumnSlotFill.runs_payload_exponent exponent modulus tail hExponent before []
  obtain ⟨u, hu, run⟩ := hCopy
  have hEmpty (bits : List Bool) : ({ Tape.ofBits bits with left := [] } : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  change RunsFor FramedColumnSlotFill.program
    ({ pc := 5, inputTape := { Tape.ofBits (exponent ++ tail) with left := before },
       outputTape := ({ Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with left := [] } : Tape).moveRight } : Configuration)
    { pc := 16,
      inputTape := { Tape.ofBits tail with left := exponent.reverse.map some ++ before },
      outputTape := { left := none ::
        (BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus).reverse.map some ++ [] },
      halted := true } u at run
  rw [hEmpty] at run
  have sourceRun : RunsFor FramedColumnSlotFill.program
      (payload before (exponent ++ tail) (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus))) ideal u := by
    simpa [payload, ideal] using run
  obtain ⟨used, hUsed, wrapped⟩ := wrap_run before (exponent ++ tail)
    (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)) ideal u sourceRun rfl
  exact ⟨{ ideal.resumeAt finalPc with halted := true }, used,
    by omega, wrapped, rfl, rfl, rfl⟩

theorem runs_into_first (first exponent modulus tail : List Bool)
    (hFirst : first.length = modulus.length)
    (hExponent : exponent.length = modulus.length) (before : List (Option Bool)) :
    ∃ target used, used ≤ 9 * exponent.length + 5 ∧
      RunsFor program
        (entry before (exponent ++ tail) (Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus)))
        target used ∧ target.halted = true ∧
      target.inputTape = { Tape.ofBits tail with left := exponent.reverse.map some ++ before } ∧
      target.outputTape = { left := none ::
        (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some } := by
  let ideal : Configuration :=
    { pc := 16,
      inputTape := { Tape.ofBits tail with left := exponent.reverse.map some ++ before },
      outputTape := { left := none ::
        (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some },
      halted := true }
  have hCopy := FramedColumnSlotFill.runs_payload_second first exponent modulus tail hFirst hExponent before []
  obtain ⟨u, hu, run⟩ := hCopy
  have hEmpty (bits : List Bool) : ({ Tape.ofBits bits with left := [] } : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  change RunsFor FramedColumnSlotFill.program
    ({ pc := 5, inputTape := { Tape.ofBits (exponent ++ tail) with left := before },
       outputTape := ({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with left := [] } : Tape).moveRight } : Configuration)
    { pc := 16,
      inputTape := { Tape.ofBits tail with left := exponent.reverse.map some ++ before },
      outputTape := { left := none ::
        (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some ++ [] },
      halted := true } u at run
  rw [hEmpty] at run
  have sourceRun : RunsFor FramedColumnSlotFill.program
      (payload before (exponent ++ tail) (Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus))) ideal u := by
    simpa [payload, ideal] using run
  obtain ⟨used, hUsed, wrapped⟩ := wrap_run before (exponent ++ tail)
    (Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus)) ideal u sourceRun rfl
  exact ⟨{ ideal.resumeAt finalPc with halted := true }, used,
    by omega, wrapped, rfl, rfl, rfl⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  have hCore : ∀ t, Instruction.randomBit t ∉ FramedColumnSlotFill.program := by
    intro t
    cases t <;> decide
  have hSource := Program.asSubroutine_no_randomBit FramedColumnSlotFill.program hCore 2 finalPc tape
  simp only [program, Program.withSubroutine, pre, List.length_cons, List.length_nil,
    List.mem_append, not_or]
  exact ⟨⟨by simp, hSource⟩, by simp⟩

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (9 * raw.length + 6) := by
  obtain ⟨target, remaining, before, used, hUsed, run, hHalt, _hInput, _hLength⟩ :=
    runs_any [] raw ({} : Tape)
  have hInitial : entry [] raw ({} : Tape) = Configuration.initial raw := by
    cases raw <;> rfl
  rw [hInitial] at run
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 9 * length + 6,
    ((PolynomiallyBounded.const 9).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 6), haltsWithin⟩

end Machine.InstanceExponentCopy
