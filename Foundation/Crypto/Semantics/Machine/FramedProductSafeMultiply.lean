import Foundation.Crypto.Semantics.Machine.FramedProductGuard
import Foundation.Crypto.Semantics.Machine.FramedProductMultiply

namespace Machine.FramedProductSafeMultiply

set_option maxRecDepth 4096

private def haltPc : Nat := FramedProductGuard.program.length + 1
private def guardReturn : Nat := haltPc + 1
private def coreStart : Nat := guardReturn + 1
private def beforeCore : Program :=
  FramedProductGuard.program.asSubroutine 0 guardReturn ++
    [.halt, .branch .output coreStart haltPc haltPc]

private theorem beforeCore_length : beforeCore.length = coreStart := by
  simp only [beforeCore, List.length_append, List.length_cons,
    List.length_nil, Program.asSubroutine_length]
  unfold coreStart guardReturn haltPc
  omega

/-- Reject malformed requests before calling the framed multiplier. The guard
returns the accepted input to its original tape and erases its counter. -/
def program : Program :=
  beforeCore ++ FramedProductMultiply.program.asSubroutine coreStart haltPc

private theorem guard_layout : program =
    Program.withSubroutine [] FramedProductGuard.program
      ([.halt, .branch .output coreStart haltPc haltPc] ++
        FramedProductMultiply.program.asSubroutine coreStart haltPc)
      guardReturn := by
  simp [program, beforeCore, Program.withSubroutine,
    List.append_assoc]

private theorem core_layout : program =
    Program.withSubroutine beforeCore
      FramedProductMultiply.program [] haltPc := by
  simp only [program, Program.withSubroutine,
    beforeCore_length, List.append_nil]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  have hGuard := Program.asSubroutine_no_randomBit _
    FramedProductGuard.no_randomBit 0 guardReturn tape
  have hCore := Program.asSubroutine_no_randomBit _
    FramedProductMultiply.no_randomBit coreStart haltPc tape
  simp [program, beforeCore, hGuard, hCore]

private theorem guard_stage (raw : List Bool) (target : Configuration)
    (used : Nat)
    (run : RunsFor FramedProductGuard.program
      (Configuration.initial raw) target used)
    (hHalt : target.halted = true) :
    ∃ steps, steps ≤ used + 1 ∧
      RunsFor program (Configuration.initial raw)
        (target.resumeAt guardReturn) steps := by
  obtain ⟨steps, hSteps, embedded⟩ :=
    run.withSubroutine_halted [] FramedProductGuard.program
      ([.halt, .branch .output coreStart haltPc haltPc] ++
        FramedProductMultiply.program.asSubroutine coreStart haltPc)
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
    FramedProductGuard.program
    [.halt, .branch .output coreStart haltPc haltPc]
    guardReturn 1
  have hIndex : guardReturn = FramedProductGuard.program.length + 1 + 1 := by
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
    FramedProductGuard.program
    [.halt, .branch .output coreStart haltPc haltPc]
    guardReturn 0
  have hIndex : haltPc = FramedProductGuard.program.length + 1 + 0 := by
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

/-- Invoke the framed multiplier on the exact tapes left by the accepting
guard. Tape equivalence allows only redundant blank cells. -/
private theorem core_stage (raw : List Bool) (start target : Configuration)
    (used : Nat)
    (hInput : start.inputTape.Equivalent (Tape.ofBits raw))
    (hOutput : start.outputTape.Equivalent ({} : Tape))
    (run : RunsFor FramedProductMultiply.program
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
    actualRun.withSubroutine_halted beforeCore FramedProductMultiply.program
      [] haltPc (Nat.zero_le _) rfl hActualHalt
  have hJoin : start.resumeAt coreStart =
      physicalStart.rebasePc beforeCore.length := by
    simp [physicalStart, Configuration.resumeAt,
      Configuration.rebasePc, beforeCore_length]
  refine ⟨actual, steps, by omega, ?_, hActualHalt,
    hEquivalent.2.2.2.symm⟩
  rw [core_layout, hJoin]
  exact embedded

/-- Split a checked instance payload into its three fixed-width fields. This
is a proof about the accepted code, not a machine-level tape operation. -/
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

/-- A fixed polynomial budget covers both malformed inputs, rejected by the
guard, and all syntactically valid inputs, including invalid numeric fields. -/
def budget (length : Nat) : Nat :=
  FramedProductGuard.budget length +
    FramedProductMultiply.validSecurityBudget length + 5

theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  exact (FramedProductGuard.budget_polynomiallyBounded.add
    FramedProductMultiply.validSecurityBudget_polynomiallyBounded).add
      (PolynomiallyBounded.const 5)

theorem runs_any (raw : List Bool) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true := by
  obtain ⟨guarded, guardUsed, hGuardUsed, guardRun, hGuardHalt,
    outcome⟩ := FramedProductGuard.runs_any raw
  have hGuardBudget : guardUsed ≤
      FramedProductGuard.budget raw.length := hGuardUsed
  obtain ⟨guardSteps, hGuardSteps, wrappedGuard⟩ :=
    guard_stage raw guarded guardUsed guardRun hGuardHalt
  rcases outcome with hMarked | ⟨_, hInput, hOutput,
    n, instanceBits, first, second, hRaw, hInstance,
    hFirst, hSecond⟩
  · have hReject := branch_reject guarded hMarked
    have hStop := halt_step guarded
    refine ⟨{ guarded.resumeAt haltPc with halted := true },
      guardSteps + 2, ?_, (wrappedGuard.succ hReject).succ hStop, rfl⟩
    change guardSteps + 2 ≤ FramedProductGuard.budget raw.length +
      FramedProductMultiply.validSecurityBudget raw.length + 5
    omega
  obtain ⟨modulus, q, g, hSplit, hModulus,
    hQ, hG⟩ := split_instance (n + 3) instanceBits hInstance
  have hQ' : q.length = modulus.length := hQ.trans hModulus.symm
  have hG' : g.length = modulus.length := hG.trans hModulus.symm
  have hFirst' : first.length = modulus.length := hFirst.trans hModulus.symm
  have hSecond' : second.length = modulus.length := hSecond.trans hModulus.symm
  obtain ⟨product, productUsed, hProductUsed, productRun,
    hProductHalt⟩ := FramedProductMultiply.runs_shaped
      n modulus q g first second hModulus hQ' hG' hFirst' hSecond'
  have hCoreRaw : raw = encodeSecurityParameter n ++
      frame (modulus ++ q ++ g) ++ frame first ++ frame second := by
    rw [hRaw, hSplit]
  obtain ⟨actual, coreSteps, hCoreSteps, coreRun,
    hActualHalt, _⟩ := core_stage raw guarded product productUsed
      hInput hOutput (by simpa only [hCoreRaw] using productRun)
      hProductHalt
  have hBlank : guarded.outputTape.current = none := hOutput.1
  have hBranch := branch_accept guarded hBlank
  have hStop := halt_step actual
  have hFixed := FramedProductMultiply.validBudget_fixedWidth
    n modulus q g first second hModulus hQ' hG' hFirst' hSecond'
  have hProductSecurity : productUsed ≤
      FramedProductMultiply.validSecurityBudget n := by
    rw [← hFixed]
    exact hProductUsed
  have hn : n ≤ raw.length := by
    rw [hCoreRaw]
    simp [encodeSecurityParameter, frame]
  have hPow : (3 * n + 13) ^ 4 ≤ (3 * raw.length + 13) ^ 4 := by
    gcongr
  have hProductRaw : productUsed ≤
      FramedProductMultiply.validSecurityBudget raw.length := by
    have hBudget : FramedProductMultiply.validSecurityBudget n ≤
        FramedProductMultiply.validSecurityBudget raw.length := by
      dsimp [FramedProductMultiply.validSecurityBudget]
      omega
    exact hProductSecurity.trans hBudget
  refine ⟨{ actual.resumeAt haltPc with halted := true },
    guardSteps + 1 + coreSteps + 1, ?_,
    ((wrappedGuard.succ hBranch).trans coreRun).succ hStop, rfl⟩
  change guardSteps + 1 + coreSteps + 1 ≤
    FramedProductGuard.budget raw.length +
      FramedProductMultiply.validSecurityBudget raw.length + 5
  omega

/-- Valid represented operands pass the guard and retain the framed
multiplier's exact modular-product output. -/
theorem runs_valid_bounded (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++
      frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ (finish : Configuration) (used : Nat),
      used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus) := by
  dsimp only
  let instanceBits := modulus ++ q ++ g
  let raw := encodeSecurityParameter n ++
    frame instanceBits ++ frame a ++ frame b
  have hInstance : instanceBits.length = 3 * (n + 3) := by
    simp [instanceBits, hModulus, hQ, hG]
    omega
  obtain ⟨guarded, guardUsed, hGuardUsed, guardRun,
    hGuardHalt, _, hGuardInput, hGuardOutput⟩ :=
    FramedProductGuard.runs_valid n instanceBits a b
      hInstance (hA.trans hModulus) (hB.trans hModulus)
  obtain ⟨guardSteps, hGuardSteps, wrappedGuard⟩ :=
    guard_stage raw guarded guardUsed guardRun hGuardHalt
  obtain ⟨product, productUsed, hProductUsed, productRun,
    hProductHalt, hProductOutput⟩ :=
    FramedProductMultiply.runs_valid_bounded n modulus q g a b
      hModulus hQ hG hA hB hOperand hModWidth
  obtain ⟨actual, coreSteps, hCoreSteps, coreRun,
    _, hProductEquiv⟩ :=
    core_stage raw guarded product productUsed
      hGuardInput hGuardOutput productRun hProductHalt
  have hBlank : guarded.outputTape.current = none := hGuardOutput.1
  have hBranch := branch_accept guarded hBlank
  have hStop := halt_step actual
  have hOutputBits : actual.outputBits = Binary.encode modulus.length
      (Binary.value a * Binary.value b % Binary.value modulus) :=
    hProductEquiv.bits.trans hProductOutput
  have hGuardBudget : guardUsed ≤ FramedProductGuard.budget raw.length :=
    hGuardUsed
  have hFixed := FramedProductMultiply.validBudget_fixedWidth
    n modulus q g a b hModulus hQ hG hA hB
  have hProductSecurity : productUsed ≤
      FramedProductMultiply.validSecurityBudget n := by
    rw [← hFixed]
    exact hProductUsed
  have hn : n ≤ raw.length := by
    simp [raw, encodeSecurityParameter, frame]
  have hPow : (3 * n + 13) ^ 4 ≤ (3 * raw.length + 13) ^ 4 := by
    gcongr
  have hProductRaw : productUsed ≤
      FramedProductMultiply.validSecurityBudget raw.length := by
    have hBudget : FramedProductMultiply.validSecurityBudget n ≤
        FramedProductMultiply.validSecurityBudget raw.length := by
      dsimp [FramedProductMultiply.validSecurityBudget]
      omega
    exact hProductSecurity.trans hBudget
  refine ⟨{ actual.resumeAt haltPc with halted := true },
    guardSteps + 1 + coreSteps + 1, ?_,
    ((wrappedGuard.succ hBranch).trans coreRun).succ hStop,
    rfl, ?_⟩
  · change guardSteps + 1 + coreSteps + 1 ≤
      FramedProductGuard.budget raw.length +
        FramedProductMultiply.validSecurityBudget raw.length + 5
    omega
  · simpa only [Configuration.resumeAt, Configuration.outputBits] using
      hOutputBits

theorem eval_valid (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++
      frame (modulus ++ q ++ g) ++ frame a ++ frame b
    evalWithin program raw (budget raw.length) =
      PMF.pure (some (Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus))) := by
  dsimp only
  obtain ⟨finish, used, hUsed, run, hHalt, hOutput⟩ :=
    runs_valid_bounded n modulus q g a b
      hModulus hQ hG hA hB hOperand hModWidth
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

end Machine.FramedProductSafeMultiply
