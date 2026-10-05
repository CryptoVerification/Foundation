import Foundation.Crypto.Semantics.Machine.ChooseOuterGuard
import Foundation.Crypto.Semantics.Machine.ChooseValidationRuntime

namespace Machine.ChooseSafeValidation

set_option maxRecDepth 4096

private def haltPc : Nat := ChooseOuterGuard.program.length + 1
private def guardReturn : Nat := haltPc + 1
private def coreStart : Nat := guardReturn + 1
private def beforeCore : Program :=
  ChooseOuterGuard.program.asSubroutine 0 guardReturn ++
    [.halt, .branch .output coreStart haltPc haltPc]

private theorem beforeCore_length : beforeCore.length = coreStart := by
  simp only [beforeCore, List.length_append, List.length_cons,
    List.length_nil, Program.asSubroutine_length]
  unfold coreStart guardReturn haltPc
  omega

/-- Reject malformed requests before calling the choose-validation body. The guard
returns the accepted input to its original tape and erases its counter. -/
def program : Program :=
  beforeCore ++ ChooseValidation.program.asSubroutine coreStart haltPc

private theorem guard_layout : program =
    Program.withSubroutine [] ChooseOuterGuard.program
      ([.halt, .branch .output coreStart haltPc haltPc] ++
        ChooseValidation.program.asSubroutine coreStart haltPc)
      guardReturn := by
  simp [program, beforeCore, Program.withSubroutine,
    List.append_assoc]

private theorem core_layout : program =
    Program.withSubroutine beforeCore
      ChooseValidation.program [] haltPc := by
  simp only [program, Program.withSubroutine,
    beforeCore_length, List.append_nil]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  have hGuard := Program.asSubroutine_no_randomBit _
    ChooseOuterGuard.no_randomBit 0 guardReturn tape
  have hCore := Program.asSubroutine_no_randomBit _
    ChooseValidation.no_randomBit coreStart haltPc tape
  simp [program, beforeCore, hGuard, hCore]

private theorem guard_stage (raw : List Bool) (target : Configuration)
    (used : Nat)
    (run : RunsFor ChooseOuterGuard.program
      (Configuration.initial raw) target used)
    (hHalt : target.halted = true) :
    ∃ steps, steps ≤ used + 1 ∧
      RunsFor program (Configuration.initial raw)
        (target.resumeAt guardReturn) steps := by
  obtain ⟨steps, hSteps, embedded⟩ :=
    run.withSubroutine_halted [] ChooseOuterGuard.program
      ([.halt, .branch .output coreStart haltPc haltPc] ++
        ChooseValidation.program.asSubroutine coreStart haltPc)
      guardReturn (Nat.zero_le _) rfl hHalt
  refine ⟨steps, by omega, ?_⟩
  rw [guard_layout]
  simpa [Configuration.rebasePc] using embedded

private theorem branch_lookup : program[guardReturn]? =
    some (.branch .output coreStart haltPc haltPc) := by
  rw [program, List.getElem?_append_left
    (by rw [beforeCore_length]; unfold coreStart; omega)]
  unfold beforeCore
  have lookup := Program.withSubroutine_getElem?_suffix []
    ChooseOuterGuard.program
    [.halt, .branch .output coreStart haltPc haltPc]
    guardReturn 1
  have hIndex : guardReturn = ChooseOuterGuard.program.length + 1 + 1 := by
    rfl
  simpa only [Program.withSubroutine, List.length_nil, Nat.zero_add,
    Nat.add_zero, List.nil_append, ← hIndex,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
    using lookup

private theorem halt_lookup : program[haltPc]? = some .halt := by
  rw [program, List.getElem?_append_left
    (by rw [beforeCore_length]; unfold coreStart guardReturn; omega)]
  unfold beforeCore
  have lookup := Program.withSubroutine_getElem?_suffix []
    ChooseOuterGuard.program
    [.halt, .branch .output coreStart haltPc haltPc]
    guardReturn 0
  have hIndex : haltPc = ChooseOuterGuard.program.length + 1 + 0 := by
    rfl
  simpa only [Program.withSubroutine, List.length_nil, Nat.zero_add,
    Nat.add_zero, List.nil_append, ← hIndex,
    List.getElem?_cons_zero]
    using lookup

private theorem branch_accept (c : Configuration)
    (hBlank : c.outputTape.current = none) :
    Step program (c.resumeAt guardReturn)
      (c.resumeAt coreStart) := by
  simp [Step, successors, next, branch_lookup,
    Configuration.resumeAt, Configuration.tape, hBlank, Instruction.next]

private theorem branch_reject (c : Configuration)
    (hMarked : c.outputTape.current = some true) :
    Step program (c.resumeAt guardReturn)
      (c.resumeAt haltPc) := by
  simp [Step, successors, next, branch_lookup,
    Configuration.resumeAt, Configuration.tape, hMarked, Instruction.next]

private theorem halt_step (c : Configuration) :
    Step program (c.resumeAt haltPc)
      { c.resumeAt haltPc with halted := true } := by
  simp [Step, successors, next, halt_lookup,
    Configuration.resumeAt, Instruction.next]

/-- Invoke the choose-validation body on the exact tapes left by the accepting
guard. Tape equivalence allows only redundant blank cells. -/
private theorem core_stage (raw : List Bool) (start target : Configuration)
    (used : Nat)
    (hInput : start.inputTape.Equivalent (Tape.ofBits raw))
    (hOutput : start.outputTape.Equivalent ({} : Tape))
    (run : RunsFor ChooseValidation.program
      (Configuration.initial raw) target used)
    (hHalt : target.halted = true) :
    ∃ (actual : Configuration) (steps : Nat),
      steps ≤ used + 1 ∧
      RunsFor program (start.resumeAt coreStart)
        (actual.resumeAt haltPc) steps ∧
      actual.halted = true ∧
      actual.outputTape.Equivalent target.outputTape := by
  let physicalStart : Configuration :=
    { inputTape := start.inputTape, outputTape := start.outputTape }
  have hStart : (Configuration.initial raw).Equivalent physicalStart :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    run.exists_equivalent hStart
  have hActualHalt : actual.halted = true :=
    hEquivalent.2.1.symm.trans hHalt
  obtain ⟨steps, hSteps, embedded⟩ :=
    actualRun.withSubroutine_halted beforeCore ChooseValidation.program
      [] haltPc (Nat.zero_le _) rfl hActualHalt
  have hJoin : start.resumeAt coreStart =
      physicalStart.rebasePc beforeCore.length := by
    simp [physicalStart, Configuration.resumeAt,
      Configuration.rebasePc, beforeCore_length]
  refine ⟨actual, steps, by omega, ?_, hActualHalt,
    hEquivalent.2.2.2.symm⟩
  rw [core_layout, hJoin]
  exact embedded

/-- Connect the accepting outer guard to an actual halted trace of the
validation body. The original input is physically restored by the guard;
this theorem does not reconstruct the input as a machine operation. -/
theorem runs_valid (n : Nat) (instanceBits reply : List Bool)
    (hInstance : instanceBits.length = 3*(n+3))
    (next : Configuration) (bodyUsed : Nat)
    (bodyRun : RunsFor ChooseValidation.program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)) next bodyUsed)
    (bodyHalt : next.halted = true) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ (target : Configuration) (used : Nat),
      used ≤ ChooseOuterGuard.budget raw.length + bodyUsed + 4 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.outputBits = next.outputBits := by
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨guarded, guardUsed, hGuardUsed, guardRun, guardHalt, hGuardInput, hGuardOutput⟩ :=
    ChooseOuterGuard.runs_valid n instanceBits reply hInstance
  obtain ⟨u, hu, r₁⟩ := guard_stage raw guarded guardUsed guardRun guardHalt
  have hBlank : guarded.outputTape.current = none := hGuardOutput.1
  have r₂ := branch_accept guarded hBlank
  obtain ⟨actual, v, hv, r₃, _, hActualOutput⟩ :=
    core_stage raw guarded next bodyUsed hGuardInput hGuardOutput bodyRun bodyHalt
  refine ⟨{ actual.resumeAt haltPc with halted := true }, u+1+v+1, ?_,
    (((r₁.succ r₂).trans r₃).succ (halt_step actual)), rfl, ?_⟩
  · change u+1+v+1 ≤ ChooseOuterGuard.budget raw.length + bodyUsed + 4
    change guardUsed ≤ ChooseOuterGuard.budget raw.length at hGuardUsed
    omega
  · exact hActualOutput.bits

private theorem split_instance (width : Nat) (bits : List Bool)
    (hLength : bits.length = 3 * width) :
    ∃ modulus q g,
      bits = modulus ++ q ++ g ∧
      modulus.length = width ∧ q.length = width ∧ g.length = width := by
  let modulus := bits.take width
  let tail := bits.drop width
  let q := tail.take width
  let g := tail.drop width
  have hWidth : width ≤ bits.length := by omega
  have hModulus : modulus.length = width := by
    simp [modulus, List.length_take, Nat.min_eq_left hWidth]
  have hTail : tail.length = 2 * width := by
    simp [tail, List.length_drop, hLength]
    omega
  have hQ : q.length = width := by
    simp [q, List.length_take, hTail, Nat.min_eq_left (by omega : width ≤ 2 * width)]
  have hG : g.length = width := by
    simp [g, List.length_drop, hTail]
    omega
  have hBits : bits = modulus ++ q ++ g := by
    have hFirst := List.take_append_drop width bits
    have hSecond := List.take_append_drop width tail
    simpa [modulus, tail, q, g, List.append_assoc] using hFirst.symm.trans
      (congrArg (modulus ++ ·) hSecond.symm)
  exact ⟨modulus, q, g, hBits, hModulus, hQ, hG⟩

/-- Common budget for every raw input, including malformed outer frames. -/
def budget (L : Nat) : Nat :=
  ChooseOuterGuard.budget L + ChooseValidationRuntime.budget L + 4

theorem budget_polynomiallyBounded : PolynomiallyBounded budget :=
  (ChooseOuterGuard.budget_polynomiallyBounded.add
    ChooseValidationRuntime.budget_polynomiallyBounded).add (PolynomiallyBounded.const 4)

theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨guarded, guardUsed, hGuardUsed, guardRun, guardHalt, hResult⟩ :=
    ChooseOuterGuard.runs_any raw
  obtain ⟨u, hu, r₁⟩ := guard_stage raw guarded guardUsed guardRun guardHalt
  rcases hResult with hReject | ⟨hInput, hOutput, n, instanceBits, reply, hRaw, hLength⟩
  · refine ⟨{ guarded.resumeAt haltPc with halted := true }, u+1+1, ?_,
      (r₁.succ (branch_reject guarded hReject)).succ (halt_step guarded), rfl⟩
    change guardUsed ≤ ChooseOuterGuard.budget raw.length at hGuardUsed
    unfold budget
    omega
  · obtain ⟨p, q, g, hFields, hp, hq, hg⟩ := split_instance (n+3) instanceBits hLength
    obtain ⟨next, bodyUsed, hBodyUsed, bodyRun, bodyHalt⟩ :=
      ChooseValidationRuntime.runs_fields n p q g reply hp (hq.trans hp.symm) (hg.trans hp.symm)
    have hBody : RunsFor ChooseValidation.program (Configuration.initial raw) next bodyUsed := by
      simpa only [← hFields, ← hRaw] using bodyRun
    have hBodyBound : bodyUsed ≤ ChooseValidationRuntime.budget raw.length := by
      simpa only [← hFields, ← hRaw] using hBodyUsed
    obtain ⟨actual, v, hv, r₃, _, _⟩ :=
      core_stage raw guarded next bodyUsed hInput hOutput hBody bodyHalt
    refine ⟨{ actual.resumeAt haltPc with halted := true }, u+1+v+1, ?_,
      ((r₁.succ (branch_accept guarded hOutput.1)).trans r₃).succ (halt_step actual), rfl⟩
    change guardUsed ≤ ChooseOuterGuard.budget raw.length at hGuardUsed
    unfold budget
    omega

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

end Machine.ChooseSafeValidation
