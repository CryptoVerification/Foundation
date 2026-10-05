import Foundation.Machine.FramedColumnSlotFill
import Foundation.Machine.NativeInvocation

namespace Machine.InstanceBaseCopy

private def pre : Program := [.jump 6]
private def finalPc : Nat := 1 + FramedColumnSlotFill.program.length + 1

/-- Enter the existing width-bounded writer directly at its payload loop.
Only the first slot changes; an unread suffix is retained on the input. -/
def program : Program :=
  Program.withSubroutine pre FramedColumnSlotFill.program [.halt] finalPc

private def entry (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before }, outputTape := output }

private def payload (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 5, inputTape := { Tape.ofBits bits with left := before }, outputTape := output }

private theorem prefix_eval (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    evalConfigWithin program (entry before bits output) 1 =
      PMF.pure ((payload before bits output).rebasePc 1) := by
  simp [evalConfigWithin, stepPMF, next, program, pre, Program.withSubroutine,
    entry, payload, Configuration.rebasePc, Instruction.next, Configuration.advance,
    Configuration.updateTape, PMF.pure_bind]

private theorem wrap_run (before : List (Option Bool)) (bits : List Bool) (output : Tape)
    (target : Configuration) (used : Nat)
    (run : RunsFor FramedColumnSlotFill.program (payload before bits output) target used)
    (hHalt : target.halted = true) :
    ∃ consumed, consumed ≤ used + 2 ∧
      RunsFor program (entry before bits output)
        { target.resumeAt finalPc with halted := true } consumed := by
  have hSupport : ((payload before bits output).rebasePc 1) ∈
      (evalConfigWithin program (entry before bits output) 1).support := by
    rw [prefix_eval]
    simp
  obtain ⟨u, hu, prefixRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  obtain ⟨v, hv, embedded⟩ := run.withSubroutine_halted pre
    FramedColumnSlotFill.program [.halt] finalPc (by change 5 ≤ 17; decide) rfl hHalt
  have hSource : RunsFor program ((payload before bits output).rebasePc 1)
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

/-- Replace the first operand while preserving the previously populated
exponent, modulus, and unread request suffix. -/
theorem runs_first (old first exponent modulus tail : List Bool)
    (hOld : old.length = modulus.length) (hFirst : first.length = modulus.length)
    (hExponent : exponent.length = modulus.length) (before : List (Option Bool)) :
    ∃ target used, used ≤ 9*first.length+4 ∧
      RunsFor program
        ({inputTape := {Tape.ofBits (first++tail) with left := before}, outputTape := Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape = {Tape.ofBits tail with left := first.reverse.map some ++ before} ∧
      target.outputTape = {left := (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some} := by
  let target : Configuration := {pc := 16, inputTape := {Tape.ofBits tail with left := first.reverse.map some ++ before}, outputTape := {left := (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some}, halted := true}
  have ev := FramedColumnSlotFill.payload_replace_first old first exponent modulus tail
    hOld hFirst hExponent before []
  have empty (bits : List Bool) : ({Tape.ofBits bits with left := []} : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  change evalConfigWithin FramedColumnSlotFill.program
    ({pc := 5, inputTape := {Tape.ofBits (first++tail) with left := before}, outputTape := {Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus) with left := []}} : Configuration)
    (9*first.length+2) = PMF.pure
      {pc := 16, inputTape := {Tape.ofBits tail with left := first.reverse.map some ++ before}, outputTape := {left := (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some ++ []}, halted := true} at ev
  rw [empty, List.append_nil] at ev
  have support : target ∈ (evalConfigWithin FramedColumnSlotFill.program
      (payload before (first++tail) (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (9*first.length+2)).support := by
    change evalConfigWithin FramedColumnSlotFill.program
      (payload before (first++tail) (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)))
      (9*first.length+2) = PMF.pure target at ev
    rw [ev]
    simp
  obtain ⟨u, hu, run⟩ := ((mem_support_evalConfigWithin_iff _ _ _ _).mp support).toRunsFor_le
  obtain ⟨used, bound, wrapped⟩ := wrap_run before (first++tail)
    (Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus)) target u run rfl
  exact ⟨{target.resumeAt finalPc with halted := true}, used, by omega, wrapped, rfl, rfl, rfl⟩

theorem runs_first_template (first modulus tail : List Bool)
    (hFirst : first.length = modulus.length) (before : List (Option Bool)) :
    ∃ target used, used ≤ 9*first.length+4 ∧
      RunsFor program
        ({inputTape := {Tape.ofBits (first++tail) with left := before}, outputTape := Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape = {Tape.ofBits tail with left := first.reverse.map some ++ before} ∧
      target.outputTape = {left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some} := by
  let target : Configuration := {pc := 16, inputTape := {Tape.ofBits tail with left := first.reverse.map some ++ before}, outputTape := {left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some}, halted := true}
  have ev := FramedColumnSlotFill.payload_first first modulus tail hFirst before []
  have empty (bits : List Bool) : ({Tape.ofBits bits with left := []} : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  change evalConfigWithin FramedColumnSlotFill.program
    ({pc := 5, inputTape := {Tape.ofBits (first++tail) with left := before}, outputTape := {Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with left := []}} : Configuration)
    (9*first.length+2) = PMF.pure
      {pc := 16, inputTape := {Tape.ofBits tail with left := first.reverse.map some ++ before}, outputTape := {left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some ++ []}, halted := true} at ev
  rw [empty, List.append_nil] at ev
  have support : target ∈ (evalConfigWithin FramedColumnSlotFill.program
      (payload before (first++tail) (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)))
      (9*first.length+2)).support := by
    change evalConfigWithin FramedColumnSlotFill.program
      (payload before (first++tail) (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)))
      (9*first.length+2) = PMF.pure target at ev
    rw [ev]
    simp
  obtain ⟨u, hu, run⟩ := ((mem_support_evalConfigWithin_iff _ _ _ _).mp support).toRunsFor_le
  obtain ⟨used, bound, wrapped⟩ := wrap_run before (first++tail)
    (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)) target u run rfl
  exact ⟨{target.resumeAt finalPc with halted := true}, used, by omega, wrapped, rfl, rfl, rfl⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  have hCore : ∀ t, Instruction.randomBit t ∉ FramedColumnSlotFill.program := by
    intro t
    cases t <;> decide
  have hSource := Program.asSubroutine_no_randomBit FramedColumnSlotFill.program hCore 1 finalPc tape
  simp only [program, Program.withSubroutine, pre, List.length_cons, List.length_nil,
    List.mem_append, not_or]
  exact ⟨⟨by simp, hSource⟩, by simp⟩

end Machine.InstanceBaseCopy
