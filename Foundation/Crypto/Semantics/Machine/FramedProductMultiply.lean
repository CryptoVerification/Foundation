import Foundation.Crypto.Semantics.Machine.FramedProductInput
import Foundation.Crypto.Semantics.Machine.BinaryProductExternalWidth

namespace Machine.FramedProductMultiply

private def firstReturn : Nat := FramedProductInput.program.length + 1
private def first : Program := FramedProductInput.program.asSubroutine 0 firstReturn
private def finalReturn (core : Program) : Nat := first.length + core.length + 1

/-- The framed parser and the bit-level modular multiplier share one physical
input/output tape pair. No multiplication or tape conversion is performed by
the meta-level proof. -/
def withCore (core : Program) : Program :=
  first ++ core.asSubroutine firstReturn (finalReturn core) ++ [.halt]

def program : Program := withCore BinaryProductExternalWidth.program

/-- The budget for a valid framed request is the parser budget plus the
raw multiplier budget and the two subroutine returns and final halt. -/
def validBudget (n : Nat) (modulus q g a b : List Bool) : Nat :=
  FramedProductInput.validBudget n modulus q g a b +
    BinaryProductExternalWidth.budget
      (BinaryColumnSlotFill.fullSlots a b modulus).length + 3

def validSecurityBudget (n : Nat) : Nat :=
  183 * n + 658 + 1000000 * (3 * n + 13) ^ 4

/-- One budget indexed by total raw input length. It covers all correctly
framed requests; all-input stopping of the composed multiplier remains a
separate obligation. -/
def rawBudget (length : Nat) : Nat := validSecurityBudget length

theorem validSecurityBudget_polynomiallyBounded :
    PolynomiallyBounded validSecurityBudget := by
  change PolynomiallyBounded
    (fun n => 183 * n + 658 + 1000000 * (3 * n + 13) ^ 4)
  exact (((PolynomiallyBounded.const 183).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 658)).add
      ((PolynomiallyBounded.const 1000000).mul
        ((((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add
          (PolynomiallyBounded.const 13)).pow 4))

theorem rawBudget_polynomiallyBounded : PolynomiallyBounded rawBudget :=
  validSecurityBudget_polynomiallyBounded

/-- On fixed-width fields, the valid-request budget depends only on the
security parameter. This is an explicit quartic bound on the whole trace. -/
theorem validBudget_fixedWidth (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length) :
    validBudget n modulus q g a b = validSecurityBudget n := by
  have hThird : (BinaryThirdColumnTemplate.columns modulus).length =
      3 * (n + 3) := by
    rw [BinaryThirdColumnTemplate.columns,
      BinaryProductSemantics.interleave_length]
    simp [hModulus]
  have hFirst : (BinaryColumnSlotFill.firstSlots a modulus).length =
      3 * (n + 3) := by
    rw [BinaryColumnSlotFill.firstSlots,
      BinaryProductSemantics.interleave_length]
    simp [hA, hModulus]
  have hFull : (BinaryColumnSlotFill.fullSlots a b modulus).length =
      3 * (n + 3) := by
    rw [BinaryColumnSlotFill.fullSlots,
      BinaryProductSemantics.interleave_length]
    simp [hA, hB, hModulus]
  have hRaw : (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++
      frame a ++ frame b).length = 11 * n + 34 := by
    simp [encodeSecurityParameter, frame, hModulus, hQ, hG, hA, hB]
    omega
  simp only [validBudget, validSecurityBudget, FramedProductInput.validBudget,
    FramedProductColumns.validBudget,
    FramedFirstColumnPreparation.validBudget,
    FramedInstanceColumnPreparation.validBudget,
    BinaryProductExternalWidth.budget, BinaryProductPadded.budget,
    BinaryWorkspacePreparation.budget, BinaryProductProgram.budget]
  rw [hFull, hFirst, hThird, hRaw]
  simp only [List.length_append, hModulus, hQ, hG]
  have hPowerArg : 3 * (n + 3) + 3 + 1 = 3 * n + 13 := by omega
  rw [hPowerArg]
  omega

/-- The concrete finite wrapper contains no random instruction. This fact is
checked on its actual instruction list, including the embedded core. -/
theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] FramedProductInput.program
      (core.asSubroutine firstReturn (finalReturn core) ++ [.halt])
      firstReturn := by
  simp [withCore, first, firstReturn, Program.withSubroutine, List.append_assoc]

private theorem first_length : first.length = firstReturn := by
  simp [first, firstReturn]

private theorem second_layout (core : Program) : withCore core =
    Program.withSubroutine first core [.halt] (finalReturn core) := by
  simp [withCore, Program.withSubroutine, first_length]

private theorem final_return_eq (core : Program) :
    finalReturn core = first.length + core.length + 1 := rfl

private theorem append_halt_step (p : Program) (c : Configuration)
    (hPc : c.pc = p.length) (hActive : c.halted = false) :
    Step (p ++ [.halt]) c { c with halted := true } := by
  have hLookup : (p ++ [.halt])[c.pc]? = some .halt := by
    rw [hPc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  simp [Step, successors, next, hActive, hLookup, Instruction.next]

private theorem subroutine_body_length (preCode core : Program) (base ret : Nat) :
    (preCode ++ core.asSubroutine base ret).length = preCode.length + core.length + 1 := by
  simp only [List.length_append, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (core : Program) (c : Configuration)
    (hPc : c.pc = finalReturn core) (hActive : c.halted = false) :
    Step (withCore core) c { c with halted := true } := by
  let body := first ++ core.asSubroutine firstReturn (finalReturn core)
  have hLength : body.length = finalReturn core := by
    exact (subroutine_body_length first core
      firstReturn (finalReturn core)).trans (final_return_eq core).symm
  have hStep := append_halt_step body c (hPc.trans hLength.symm) hActive
  change Step (body ++ [.halt]) c { c with halted := true }
  exact hStep

/-- A framed-parser trace can invoke the raw multiplier with arbitrary
caller cells behind the separating blank. The only required physical
interface is a contiguous raw input suffix and a blank output tape. -/
theorem runs_from_prepared (raw bits : List Bool) (before : List (Option Bool))
    (prepared : Configuration) (parserSteps : Nat)
    (hParser : RunsFor FramedProductInput.program
      (Configuration.initial raw) prepared parserSteps)
    (hParserHalt : prepared.halted = true)
    (hInput : prepared.inputTape.Equivalent
      { Tape.ofBits bits with left := none :: before })
    (hOutput : prepared.outputTape.Equivalent ({} : Tape)) :
    ∃ target used,
      used ≤ parserSteps + BinaryProductExternalWidth.budget bits.length + 3 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨v1, hv1, embedded1⟩ := hParser.withSubroutine_halted
    [] FramedProductInput.program
    (BinaryProductExternalWidth.program.asSubroutine firstReturn
      (finalReturn BinaryProductExternalWidth.program) ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hParserHalt
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    change RunsFor (withCore BinaryProductExternalWidth.program) _ _ v1
    rw [first_layout BinaryProductExternalWidth.program]
    simpa only [program, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embedded1
  obtain ⟨_, canonical, u2, _, hu2, run2, hHalt2, _⟩ :=
    BinaryProductExternalWidth.runs_with_saved bits before
  let actualStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  have hStart :
      ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration).Equivalent
        actualStart :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actualProduct, actualRun, hProductEquiv⟩ :=
    run2.exists_equivalent hStart
  have hActualHalt : actualProduct.halted = true :=
    hProductEquiv.2.1.symm.trans hHalt2
  obtain ⟨v2, hv2, embedded2⟩ := actualRun.withSubroutine_halted
    first BinaryProductExternalWidth.program [.halt]
    (finalReturn BinaryProductExternalWidth.program)
    (Nat.zero_le _) rfl hActualHalt
  have hJoin : prepared.resumeAt firstReturn =
      actualStart.rebasePc first.length := by
    simp [actualStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (actualProduct.resumeAt (finalReturn BinaryProductExternalWidth.program)) v2 := by
    change RunsFor (withCore BinaryProductExternalWidth.program) _ _ v2
    rw [hJoin, second_layout BinaryProductExternalWidth.program]
    exact embedded2
  have hStop : Step program
      (actualProduct.resumeAt (finalReturn BinaryProductExternalWidth.program))
      { actualProduct.resumeAt (finalReturn BinaryProductExternalWidth.program) with halted := true } :=
    final_step BinaryProductExternalWidth.program _ rfl rfl
  refine ⟨{ actualProduct.resumeAt (finalReturn BinaryProductExternalWidth.program) with
      halted := true }, v1 + v2 + 1, ?_, (r1.trans r2).succ hStop, rfl⟩
  omega

/-- A syntactically well-framed request terminates even when its numeric
fields do not describe a valid group. The raw multiplier's all-input bound
is used after the parser has prepared the actual tape. -/
theorem runs_shaped (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length) :
    let raw := encodeSecurityParameter n ++
      frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ target used,
      used ≤ FramedProductInput.validBudget n modulus q g a b +
        BinaryProductExternalWidth.budget
          (BinaryColumnSlotFill.fullSlots a b modulus).length + 3 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  dsimp only
  let raw := encodeSecurityParameter n ++
    frame (modulus ++ q ++ g) ++ frame a ++ frame b
  let bits := BinaryColumnSlotFill.fullSlots a b modulus
  obtain ⟨prepared, parserSteps, hParserSteps, parserRun,
    hParserHalt, hInput, hOutput⟩ :=
    FramedProductInput.runs_valid_bounded n modulus q g a b
      hModulus hQ hG hA hB
  have hBlankLeft : (Tape.ofBits bits).Equivalent
      { Tape.ofBits bits with left := [none] } := by
    refine ⟨rfl, ?_, fun _ => rfl⟩
    intro i
    cases bits with
    | nil => cases i <;> rfl
    | cons bit rest => cases i <;> rfl
  have hInput' : prepared.inputTape.Equivalent
      { Tape.ofBits bits with left := [none] } :=
    hInput.trans hBlankLeft
  obtain ⟨target, used, hUsed, run, hHalt⟩ :=
    runs_from_prepared raw bits [] prepared parserSteps
      parserRun hParserHalt hInput' hOutput
  refine ⟨target, used, ?_, run, hHalt⟩
  change used ≤ FramedProductInput.validBudget n modulus q g a b +
    BinaryProductExternalWidth.budget bits.length + 3
  omega

/-- Connect a fixed core program to the physical framed parser. The core's
canonical trace is transported to the parser's actual tapes. -/
theorem runs_from_raw (core : Program) (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (coreBudget : Nat)
    (hCore : ∃ target used,
      used ≤ coreBudget ∧
      RunsFor core (Configuration.initial (BinaryColumnSlotFill.fullSlots a b modulus)) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus)) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ target used,
      used ≤ FramedProductInput.validBudget n modulus q g a b + coreBudget + 3 ∧
      RunsFor (withCore core) (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
  let bits := BinaryColumnSlotFill.fullSlots a b modulus
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    FramedProductInput.runs_valid_bounded n modulus q g a b hModulus hQ hG hA hB
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedProductInput.program
    (core.asSubroutine firstReturn (finalReturn core) ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor (withCore core) (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout core]
    simpa [raw, Configuration.rebasePc] using embedded1
  obtain ⟨multiplied, u2, hu2, run2, hHalt2, hProduct⟩ := hCore
  let actualStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  have hStart : (Configuration.initial bits).Equivalent actualStart := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [bits, Configuration.initial, actualStart] using hInput1.symm
    · simpa [Configuration.initial, actualStart] using hOutput1.symm
  obtain ⟨actualProduct, actualRun, hProductEquiv⟩ :=
    (show RunsFor core (Configuration.initial bits) multiplied u2 from run2).exists_equivalent hStart
  have hActualHalt : actualProduct.halted = true :=
    hProductEquiv.2.1.symm.trans hHalt2
  obtain ⟨v2, hv2, embedded2⟩ := actualRun.withSubroutine_halted
    first core [.halt] (finalReturn core)
    (Nat.zero_le _) rfl hActualHalt
  have hJoin : prepared.resumeAt firstReturn = actualStart.rebasePc first.length := by
    simp [actualStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor (withCore core) (prepared.resumeAt firstReturn)
      (actualProduct.resumeAt (finalReturn core)) v2 := by
    rw [hJoin, second_layout core]
    exact embedded2
  have hStop : Step (withCore core) (actualProduct.resumeAt (finalReturn core))
      { actualProduct.resumeAt (finalReturn core) with halted := true } :=
    final_step core _ rfl rfl
  refine ⟨{ actualProduct.resumeAt (finalReturn core) with halted := true },
    v1 + v2 + 1, ?_, (r1.trans r2).succ hStop, rfl, ?_⟩
  · omega
  have hBits : actualProduct.outputBits = multiplied.outputBits :=
    hProductEquiv.2.2.2.bits.symm
  change actualProduct.outputBits = Binary.encode modulus.length
    (Binary.value a * Binary.value b % Binary.value modulus)
  exact hBits.trans hProduct

/-- On a valid fixed-width framed request, the complete finite program
returns the encoded modular product through the actual raw multiplier. -/
theorem runs_valid_bounded (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ target used,
      used ≤ validBudget n modulus q g a b ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus) := by
  let columns := (a.zip b).zip modulus
  have hPair : (a.zip b).length = modulus.length := by simp [hA, hB]
  have hFirst : columns.map (fun c => c.1.1) = a := by
    calc
      columns.map (fun c => c.1.1) =
          (((a.zip b).zip modulus).map Prod.fst).map Prod.fst := by
            simp only [List.map_map]
            rfl
      _ = a := by
        rw [List.map_fst_zip (by omega : (a.zip b).length ≤ modulus.length),
          List.map_fst_zip (by omega : a.length ≤ b.length)]
  have hSecond : columns.map (fun c => c.1.2) = b := by
    calc
      columns.map (fun c => c.1.2) =
          (((a.zip b).zip modulus).map Prod.fst).map Prod.snd := by
            simp only [List.map_map]
            rfl
      _ = b := by
        rw [List.map_fst_zip (by omega : (a.zip b).length ≤ modulus.length),
          List.map_snd_zip (by omega : b.length ≤ a.length)]
  have hMod : columns.map Prod.snd = modulus := by
    change ((a.zip b).zip modulus).map Prod.snd = modulus
    exact List.map_snd_zip (by omega : modulus.length ≤ (a.zip b).length)
  have hLength : columns.length = modulus.length := by simp [columns, hPair]
  obtain ⟨multiplied, used, hUsed, run, hHalt, hOutput⟩ :=
    BinaryProductExternalWidth.runs_product columns
      (by simpa only [hFirst, hMod] using hOperand)
      (by simpa only [hLength, hMod] using hModWidth)
  have hCore : ∃ target used,
      used ≤ BinaryProductExternalWidth.budget
        (BinaryColumnSlotFill.fullSlots a b modulus).length ∧
      RunsFor BinaryProductExternalWidth.program
        (Configuration.initial (BinaryColumnSlotFill.fullSlots a b modulus)) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus) := by
    refine ⟨multiplied, used, ?_, ?_, hHalt, ?_⟩
    · simpa only [BinaryColumnSlotFill.fullSlots, BinaryModularAddition.interleave,
        hLength, hFirst, hSecond, hMod] using hUsed
    · exact run
    · simpa only [hLength, hFirst, hSecond, hMod] using hOutput
  exact runs_from_raw BinaryProductExternalWidth.program n modulus q g a b
    hModulus hQ hG hA hB
    (BinaryProductExternalWidth.budget
      (BinaryColumnSlotFill.fullSlots a b modulus).length) hCore

theorem runs_valid (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits = Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus) := by
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    runs_valid_bounded n modulus q g a b hModulus hQ hG hA hB hOperand hModWidth
  exact ⟨target, used, run, hHalt, hOutput⟩

/-- The valid framed computation has the expected evaluator output at its
actual stopping time. A uniform polynomial stopping budget for every raw
input remains a separate obligation. -/
theorem eval_valid_at_used (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
    ∃ used,
      evalWithin program raw used = PMF.pure (some
        (Binary.encode modulus.length
          (Binary.value a * Binary.value b % Binary.value modulus))) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hOutput⟩ :=
    runs_valid n modulus q g a b hModulus hQ hG hA hB hOperand hModWidth
  refine ⟨used, ?_⟩
  unfold evalWithin
  rw [run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

/-- A valid request is correct at the explicit composed parser-and-product
budget, rather than at an existential stopping time. -/
theorem eval_valid_at_budget (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    evalWithin program
      (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b)
      (validBudget n modulus q g a b) =
        PMF.pure (some (Binary.encode modulus.length
          (Binary.value a * Binary.value b % Binary.value modulus))) := by
  obtain ⟨target, used, hUsed, run, hHalt, hOutput⟩ :=
    runs_valid_bounded n modulus q g a b hModulus hQ hG hA hB hOperand hModWidth
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

theorem eval_valid_at_securityBudget (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    evalWithin program
      (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b)
      (validSecurityBudget n) =
        PMF.pure (some (Binary.encode modulus.length
          (Binary.value a * Binary.value b % Binary.value modulus))) := by
  rw [← validBudget_fixedWidth n modulus q g a b hModulus hQ hG hA hB]
  exact eval_valid_at_budget n modulus q g a b
    hModulus hQ hG hA hB hOperand hModWidth

/-- The evaluator of a well-formed request is correct at the polynomial
budget indexed by the length actually supplied to the machine. -/
theorem eval_valid_at_rawBudget (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length)
    (hOperand : Binary.value a < Binary.value modulus)
    (hModWidth : Binary.value modulus < 2 ^ modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
    evalWithin program raw (rawBudget raw.length) =
      PMF.pure (some (Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus))) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b
  have hLength : n ≤ raw.length := by
    simp only [raw, List.length_append]
    simp [encodeSecurityParameter, frame]
    omega
  have hPow : (3 * n + 13) ^ 4 ≤ (3 * raw.length + 13) ^ 4 := by
    gcongr
  have hBudget : validSecurityBudget n ≤ rawBudget raw.length := by
    dsimp [rawBudget, validSecurityBudget]
    omega
  obtain ⟨target, used, hUsed, run, hHalt, hOutput⟩ :=
    runs_valid_bounded n modulus q g a b
      hModulus hQ hG hA hB hOperand hModWidth
  have hFixed := validBudget_fixedWidth n modulus q g a b
    hModulus hQ hG hA hB
  have hUsed' : used ≤ rawBudget raw.length := by
    rw [hFixed] at hUsed
    exact hUsed.trans hBudget
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed' hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

/-- Any budget covering a valid halted trace yields the same exact output.
This isolates the remaining task to a uniform polynomial bound on the trace
and on all malformed inputs. -/
theorem eval_valid_of_trace_bound (n : Nat) (modulus q g a b : List Bool)
    (budget : Nat) (target : Configuration) (used : Nat)
    (hUsed : used ≤ budget)
    (run : RunsFor program
      (Configuration.initial
        (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b))
      target used)
    (hHalt : target.halted = true)
    (hOutput : target.outputBits = Binary.encode modulus.length
      (Binary.value a * Binary.value b % Binary.value modulus)) :
    evalWithin program
      (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++ frame a ++ frame b)
      budget = PMF.pure (some (Binary.encode modulus.length
        (Binary.value a * Binary.value b % Binary.value modulus))) := by
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

end Machine.FramedProductMultiply
