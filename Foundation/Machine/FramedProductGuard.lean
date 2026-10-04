import Foundation.Machine.FrameWidthCheckThree
import Foundation.Machine.BitstringErasure

namespace Machine.FramedProductGuard

/-- Prefix lengths in the fixed finite verifier. Every offset is computed
from the instruction lists; no input-dependent code is generated. -/
private def templateEnd : Nat := SecurityWidthTemplate.program.length + 1
private def firstRewindEnd : Nat := templateEnd + rewindBitstring.swapTapes.length + 1
private def instanceCheckEnd : Nat := firstRewindEnd + FrameWidthCheck.program.length + 1
private def secondRewindStart : Nat := instanceCheckEnd + 1
private def secondRewindEnd : Nat := secondRewindStart + rewindBitstring.swapTapes.length + 1
private def firstElementCheckEnd : Nat := secondRewindEnd + FrameWidthCheckThree.program.length + 1
private def thirdRewindStart : Nat := firstElementCheckEnd + 1
private def thirdRewindEnd : Nat := thirdRewindStart + rewindBitstring.swapTapes.length + 1
private def secondElementCheckEnd : Nat := thirdRewindEnd + FrameWidthCheckThree.program.length + 1
private def tailCheck : Nat := secondElementCheckEnd + 1
private def eraseStart : Nat := tailCheck + 1
private def eraseEnd : Nat := eraseStart + eraseOutputBlock.length + 1
private def inputRewindEnd : Nat := eraseEnd + rewindBitstring.length + 1
private def rejectWrite : Nat := inputRewindEnd + 1
private def rejectHalt : Nat := rejectWrite + 2

private def finishCode : Program :=
  [.halt, .write .output true, .jump rejectHalt, .halt]

private def afterErase : Program :=
  rewindBitstring.asSubroutine eraseEnd inputRewindEnd ++ finishCode

private def afterSecondElement : Program :=
  [.branch .output tailCheck rejectHalt rejectHalt,
   .branch .input eraseStart rejectWrite rejectWrite] ++
  eraseOutputBlock.asSubroutine eraseStart eraseEnd ++ afterErase

private def afterThirdRewind : Program :=
  FrameWidthCheckThree.program.asSubroutine thirdRewindEnd secondElementCheckEnd ++
    afterSecondElement

private def afterFirstElement : Program :=
  [.branch .output thirdRewindStart rejectHalt rejectHalt] ++
    rewindBitstring.swapTapes.asSubroutine thirdRewindStart thirdRewindEnd ++
    afterThirdRewind

private def afterSecondRewind : Program :=
  FrameWidthCheckThree.program.asSubroutine secondRewindEnd firstElementCheckEnd ++
    afterFirstElement

private def afterInstance : Program :=
  [.branch .output secondRewindStart rejectHalt rejectHalt] ++
    rewindBitstring.swapTapes.asSubroutine secondRewindStart secondRewindEnd ++
    afterSecondRewind

private def afterFirstRewind : Program :=
  FrameWidthCheck.program.asSubroutine firstRewindEnd instanceCheckEnd ++
    afterInstance

private def postTemplate : Program :=
  rewindBitstring.swapTapes.asSubroutine templateEnd firstRewindEnd ++
    afterFirstRewind

/-- Check the unary security prefix, one `3*(n+3)`-bit instance frame, and
two `(n+3)`-bit element frames. A rejection leaves `some true` at the output
head. Acceptance erases the counter and rewinds the request to its first bit,
so that the existing framed multiplier can run on the same physical tapes. -/
def program : Program :=
  SecurityWidthTemplate.program.asSubroutine 0 templateEnd ++ postTemplate

private theorem template_layout : program =
    Program.withSubroutine [] SecurityWidthTemplate.program postTemplate templateEnd := by
  rfl

theorem length : program.length = rejectHalt + 1 := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, afterFirstElement, afterThirdRewind,
    afterSecondElement, afterErase, finishCode,
    List.length_append, List.length_cons, List.length_nil,
    Program.asSubroutine_length]
  unfold rejectHalt rejectWrite inputRewindEnd eraseEnd eraseStart tailCheck
    secondElementCheckEnd thirdRewindEnd thirdRewindStart firstElementCheckEnd
    secondRewindEnd secondRewindStart instanceCheckEnd firstRewindEnd templateEnd
  omega

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

/-- The first component writes the physical three-column counter from the
security prefix. It returns to the verifier without changing either tape. -/
private theorem template_stage (raw : List Bool) :
    ∃ (target : Configuration) (used width : Nat) (rest : List Bool)
        (before : List (Option Bool)),
      used ≤ 9 * raw.length + 21 ∧
      width ≤ raw.length + 3 ∧
      RunsFor program (Configuration.initial raw)
        (target.resumeAt templateEnd) used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits rest with left := before } ∧
      target.outputTape =
        { left := List.replicate (3 * width) (some false) } ∧
      rest.length ≤ raw.length ∧
      (rest ≠ [] → ∃ n,
        raw = encodeSecurityParameter n ++ rest ∧
        width = n + 3 ∧
        before = some false :: List.replicate n (some true)) := by
  obtain ⟨target, used, width, rest, before, hUsed, hWidth, run,
    hHalt, hInput, hOutput, hRest, hPrefix⟩ :=
      SecurityWidthTemplate.runs_any_layout_prefix raw
  obtain ⟨returnedSteps, hReturnedSteps, returned⟩ :=
    run.withSubroutine_halted [] SecurityWidthTemplate.program postTemplate
      templateEnd (Nat.zero_le _) rfl hHalt
  refine ⟨target, returnedSteps, width, rest, before, by omega,
    hWidth, ?_, hHalt, hInput, hOutput, hRest, hPrefix⟩
  rw [template_layout]
  simpa [Configuration.rebasePc] using returned

private theorem template_valid_stage (n : Nat) (rest : List Bool) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 9 * n + 22 ∧
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++ rest))
        (target.resumeAt templateEnd) used ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := some false :: List.replicate n (some true) } ∧
      target.outputTape =
        { left := List.replicate (3 * (n + 3)) (some false) } := by
  obtain ⟨target, steps, hSteps, run, hHalted, hInput, hOutput⟩ :=
    SecurityWidthTemplate.runs_valid n rest
  obtain ⟨used, hUsed, embedded⟩ :=
    run.withSubroutine_halted [] SecurityWidthTemplate.program postTemplate
      templateEnd (Nat.zero_le _) rfl hHalted
  refine ⟨target, used, by omega, ?_, hInput, hOutput⟩
  rw [template_layout]
  simpa [Configuration.rebasePc] using embedded

private theorem rewind_counter (count : Nat) (input : Tape) :
    ∃ target : Configuration,
      RunsFor rewindBitstring.swapTapes
        ({ inputTape := input,
           outputTape := { left := List.replicate count (some false) } } : Configuration)
        target (2 * count + 4) ∧
      target.halted = true ∧
      target.inputTape = input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  let target :=
    (rewindBitstringFinish (List.replicate count false) input).swapTapes
  refine ⟨target, ?_, rfl, rfl, ?_⟩
  · simpa [target, rewindBitstringStart, List.map_replicate,
      List.reverse_replicate, Configuration.swapTapes] using
        (rewindBitstring_runs (List.replicate count false) input).swapTapes
  · simpa [target, Configuration.swapTapes] using
      rewindBitstringFinish_input_equivalent (List.replicate count false) input

private theorem counter_outer_blank (count : Nat) :
    ({ left := List.replicate count (some false) ++ [none] } : Tape).Equivalent
      { left := List.replicate count (some false) } := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  induction count generalizing i with
  | zero => cases i <;> rfl
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.replicate_succ, List.cons_append,
            List.getD_cons_succ] using ih i

theorem rewind_counter_equivalent (count : Nat)
    (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * count + 4 ∧
      RunsFor rewindBitstring.swapTapes
        { inputTape := input, outputTape := output } target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨canonical, canonicalRun, hHalt, hInput, hCounter⟩ :=
    rewind_counter count input
  have hStart :
      ({ inputTape := input,
         outputTape := { left := List.replicate count (some false) } } : Configuration).Equivalent
        ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, Tape.Equivalent.refl _, hOutput.symm⟩
  obtain ⟨target, run, hEquivalent⟩ :=
    canonicalRun.exists_equivalent hStart
  exact ⟨target, 2 * count + 4, le_refl _, run,
    hEquivalent.2.1.symm.trans hHalt,
    hEquivalent.2.2.1.symm.trans (by rw [hInput]; exact Tape.Equivalent.refl _),
    hEquivalent.2.2.2.symm.trans hCounter⟩

private theorem rewind_counter_embedded (pre suffix : Program)
    (returnPc count : Nat) (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * count + 4 ∧
      RunsFor (Program.withSubroutine pre rewindBitstring.swapTapes suffix returnPc)
        { pc := pre.length, inputTape := input, outputTape := output }
        (target.resumeAt returnPc) used ∧
      target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨target, steps, hSteps, run, hHalt, hInput, hCounter⟩ :=
    rewind_counter_equivalent count input output hOutput
  obtain ⟨used, hUsed, embedded⟩ :=
    run.withSubroutine_halted pre rewindBitstring.swapTapes suffix
      returnPc (Nat.zero_le _) rfl hHalt
  exact ⟨target, used, by omega,
    by simpa [Configuration.rebasePc] using embedded,
    hHalt, hInput, hCounter⟩

private theorem first_rewind_layout : program =
    Program.withSubroutine
      (SecurityWidthTemplate.program.asSubroutine 0 templateEnd)
      rewindBitstring.swapTapes afterFirstRewind firstRewindEnd := by
  simp only [program, postTemplate, Program.withSubroutine,
    Program.asSubroutine_length]
  rfl

/-- Reposition the width counter after the security-template call. -/
private theorem first_rewind_stage (count : Nat) (input : Tape) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * count + 4 ∧
      RunsFor program
        { pc := templateEnd, inputTape := input,
          outputTape := { left := List.replicate count (some false) } }
        (target.resumeAt firstRewindEnd) used ∧
      target.halted = true ∧ target.inputTape = input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨target, run, hHalt, hInput, hOutput⟩ := rewind_counter count input
  let pre := SecurityWidthTemplate.program.asSubroutine 0 templateEnd
  obtain ⟨used, hUsed, embedded⟩ :=
    run.withSubroutine_halted pre rewindBitstring.swapTapes
      afterFirstRewind firstRewindEnd (Nat.zero_le _) rfl hHalt
  refine ⟨target, used, hUsed, ?_, hHalt, hInput, hOutput⟩
  rw [first_rewind_layout]
  have hJoin :
      ({ pc := templateEnd, inputTape := input,
         outputTape := { left := List.replicate count (some false) } } : Configuration) =
        ({ inputTape := input,
           outputTape := { left := List.replicate count (some false) } } : Configuration).rebasePc
          pre.length := by
    simp [pre, templateEnd, Program.asSubroutine_length,
      Configuration.rebasePc]
  rw [hJoin]
  exact embedded

private theorem instance_check_layout : program =
    Program.withSubroutine
      (SecurityWidthTemplate.program.asSubroutine 0 templateEnd ++
        rewindBitstring.swapTapes.asSubroutine templateEnd firstRewindEnd)
      FrameWidthCheck.program afterInstance instanceCheckEnd := by
  simp only [program, postTemplate, afterFirstRewind,
    Program.withSubroutine, List.length_append,
    Program.asSubroutine_length]
  rfl

private def beforeSecondRewind : Program :=
  SecurityWidthTemplate.program.asSubroutine 0 templateEnd ++
    rewindBitstring.swapTapes.asSubroutine templateEnd firstRewindEnd ++
    FrameWidthCheck.program.asSubroutine firstRewindEnd instanceCheckEnd ++
    [.branch .output secondRewindStart rejectHalt rejectHalt]

private theorem beforeSecondRewind_length :
    beforeSecondRewind.length = secondRewindStart := by
  simp [beforeSecondRewind, secondRewindStart, instanceCheckEnd,
    firstRewindEnd, templateEnd, Program.asSubroutine_length,
    Nat.add_assoc]

private theorem second_rewind_layout : program =
    Program.withSubroutine beforeSecondRewind rewindBitstring.swapTapes
      afterSecondRewind secondRewindEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    Program.withSubroutine]
  rw [beforeSecondRewind_length]
  simp [beforeSecondRewind, List.append_assoc]

private theorem instance_branch_lookup :
    program[instanceCheckEnd]? =
      some (.branch .output secondRewindStart rejectHalt rejectHalt) := by
  native_decide

private theorem branch_blank (pc good bad : Nat) (c : Configuration)
    (hLookup : program[pc]? = some (.branch .output good bad bad))
    (hPc : c.pc = pc) (hActive : c.halted = false)
    (hBlank : c.outputTape.current = none) :
    Step program c { c with pc := good } := by
  simp [Step, successors, next, hPc, hActive, hLookup,
    Instruction.next, Configuration.tape, hBlank]

private theorem branch_marked (pc good bad : Nat) (c : Configuration)
    (hLookup : program[pc]? = some (.branch .output good bad bad))
    (hPc : c.pc = pc) (hActive : c.halted = false)
    (hMarked : c.outputTape.current = some true) :
    Step program c { c with pc := bad } := by
  simp [Step, successors, next, hPc, hActive, hLookup,
    Instruction.next, Configuration.tape, hMarked]

private theorem second_rewind_stage (count : Nat)
    (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * count + 4 ∧
      RunsFor program
        { pc := secondRewindStart, inputTape := input, outputTape := output }
        (target.resumeAt secondRewindEnd) used ∧
      target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hCounter⟩ :=
    rewind_counter_embedded beforeSecondRewind afterSecondRewind
      secondRewindEnd count input output hOutput
  refine ⟨target, used, hUsed, ?_, hHalt, hInput, hCounter⟩
  rw [second_rewind_layout]
  simpa only [beforeSecondRewind_length] using run

private def beforeFirstElementCheck : Program :=
  beforeSecondRewind ++
    rewindBitstring.swapTapes.asSubroutine secondRewindStart secondRewindEnd

private theorem beforeFirstElementCheck_length :
    beforeFirstElementCheck.length = secondRewindEnd := by
  simp [beforeFirstElementCheck, beforeSecondRewind_length,
    secondRewindEnd, Program.asSubroutine_length, Nat.add_assoc]

private theorem first_element_layout : program =
    Program.withSubroutine beforeFirstElementCheck
      FrameWidthCheckThree.program afterFirstElement firstElementCheckEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, Program.withSubroutine]
  rw [beforeFirstElementCheck_length]
  simp [beforeFirstElementCheck, beforeSecondRewind, List.append_assoc]

/-- The three-cell checker can be embedded at either element-frame boundary.
Its output certificate is about the same physical counter used by the caller. -/
private theorem element_check_embedded (pre suffix : Program) (returnPc : Nat)
    (before : List (Option Bool)) (count : Nat) (bits : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate (3 * count) false))) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 20 * count + 12 ∧
      RunsFor
        (Program.withSubroutine pre FrameWidthCheckThree.program suffix returnPc)
        { pc := pre.length, inputTape := input, outputTape := output }
        (target.resumeAt returnPc) used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 21 then none else some true) ∧
      (target.pc = 21 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate (3 * count) (some false) ++ [none] }) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → target.pc = 21) := by
  obtain ⟨canonical, steps, hSteps, canonicalRun, hCanonicalHalt,
    hCanonicalStatus, hCanonicalAccepted⟩ :=
      FrameWidthCheckThree.runs_any_loaded before count bits
  have hStart :
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate (3 * count) false) } : Configuration).Equivalent
        ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    canonicalRun.exists_equivalent hStart
  have hActualHalt : actual.halted = true :=
    hEquivalent.2.1.symm.trans hCanonicalHalt
  obtain ⟨used, hUsed, embedded⟩ :=
    actualRun.withSubroutine_halted pre FrameWidthCheckThree.program
      suffix returnPc (Nat.zero_le _) rfl hActualHalt
  refine ⟨actual, used, by omega, ?_, hActualHalt, ?_, ?_, ?_⟩
  · simpa [Configuration.rebasePc] using embedded
  · simpa [hEquivalent.1] using
      hEquivalent.2.2.2.1.symm.trans hCanonicalStatus
  · intro hPc
    obtain ⟨payload, rest, hBits, hLength, hPosition, hCounter⟩ :=
      hCanonicalAccepted (hEquivalent.1.trans hPc)
    exact ⟨payload, rest, hBits, hLength,
      hEquivalent.2.2.1.symm.trans hPosition,
      hEquivalent.2.2.2.symm.trans hCounter⟩
  · intro payload rest hBits hLength
    subst bits
    have hCanonicalPc := FrameWidthCheckThree.accepts_valid_loaded
      before payload rest count hLength canonicalRun hCanonicalHalt
    exact hEquivalent.1.symm.trans hCanonicalPc

private theorem first_element_stage (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate (3 * count) false))) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 20 * count + 12 ∧
      RunsFor program
        { pc := secondRewindEnd, inputTape := input, outputTape := output }
        (target.resumeAt firstElementCheckEnd) used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 21 then none else some true) ∧
      (target.pc = 21 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate (3 * count) (some false) ++ [none] }) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → target.pc = 21) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, hAccepted, hValid⟩ :=
    element_check_embedded beforeFirstElementCheck afterFirstElement
      firstElementCheckEnd before count bits input output hInput hOutput
  refine ⟨target, used, hUsed, ?_, hHalt, hStatus, hAccepted, hValid⟩
  rw [first_element_layout]
  simpa only [beforeFirstElementCheck_length] using run

private theorem first_element_branch_lookup :
    program[firstElementCheckEnd]? =
      some (.branch .output thirdRewindStart rejectHalt rejectHalt) := by
  native_decide

private def beforeThirdRewind : Program :=
  beforeFirstElementCheck ++
    FrameWidthCheckThree.program.asSubroutine secondRewindEnd firstElementCheckEnd ++
    [.branch .output thirdRewindStart rejectHalt rejectHalt]

private theorem beforeThirdRewind_length :
    beforeThirdRewind.length = thirdRewindStart := by
  simp [beforeThirdRewind, beforeFirstElementCheck_length,
    thirdRewindStart, firstElementCheckEnd, Program.asSubroutine_length,
    Nat.add_assoc]

private theorem third_rewind_layout : program =
    Program.withSubroutine beforeThirdRewind rewindBitstring.swapTapes
      afterThirdRewind thirdRewindEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, afterFirstElement, Program.withSubroutine]
  rw [beforeThirdRewind_length]
  simp [beforeThirdRewind, beforeFirstElementCheck,
    beforeSecondRewind, List.append_assoc]

private theorem third_rewind_stage (count : Nat)
    (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * count + 4 ∧
      RunsFor program
        { pc := thirdRewindStart, inputTape := input, outputTape := output }
        (target.resumeAt thirdRewindEnd) used ∧
      target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent
        (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hCounter⟩ :=
    rewind_counter_embedded beforeThirdRewind afterThirdRewind
      thirdRewindEnd count input output hOutput
  refine ⟨target, used, hUsed, ?_, hHalt, hInput, hCounter⟩
  rw [third_rewind_layout]
  simpa only [beforeThirdRewind_length] using run

private def beforeSecondElementCheck : Program :=
  beforeThirdRewind ++
    rewindBitstring.swapTapes.asSubroutine thirdRewindStart thirdRewindEnd

private theorem beforeSecondElementCheck_length :
    beforeSecondElementCheck.length = thirdRewindEnd := by
  simp [beforeSecondElementCheck, beforeThirdRewind_length,
    thirdRewindEnd, Program.asSubroutine_length, Nat.add_assoc]

private theorem second_element_layout : program =
    Program.withSubroutine beforeSecondElementCheck
      FrameWidthCheckThree.program afterSecondElement secondElementCheckEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, afterFirstElement, afterThirdRewind,
    Program.withSubroutine]
  rw [beforeSecondElementCheck_length]
  simp [beforeSecondElementCheck, beforeThirdRewind,
    beforeFirstElementCheck, beforeSecondRewind, List.append_assoc]

private theorem second_element_stage (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate (3 * count) false))) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 20 * count + 12 ∧
      RunsFor program
        { pc := thirdRewindEnd, inputTape := input, outputTape := output }
        (target.resumeAt secondElementCheckEnd) used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 21 then none else some true) ∧
      (target.pc = 21 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate (3 * count) (some false) ++ [none] }) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → target.pc = 21) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, hAccepted, hValid⟩ :=
    element_check_embedded beforeSecondElementCheck afterSecondElement
      secondElementCheckEnd before count bits input output hInput hOutput
  refine ⟨target, used, hUsed, ?_, hHalt, hStatus, hAccepted, hValid⟩
  rw [second_element_layout]
  simpa only [beforeSecondElementCheck_length] using run

private theorem second_element_branch_lookup :
    program[secondElementCheckEnd]? =
      some (.branch .output tailCheck rejectHalt rejectHalt) := by
  native_decide

private theorem reject_halt_lookup : program[rejectHalt]? = some .halt := by
  native_decide

private theorem reject_halt_step (c : Configuration)
    (hPc : c.pc = rejectHalt) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  simp [Step, successors, next, hPc, hActive, reject_halt_lookup,
    Instruction.next]

/-- A marked checker return takes the finite rejection exit immediately. -/
private theorem reject_marked (pc good : Nat) (c : Configuration)
    (hLookup : program[pc]? =
      some (.branch .output good rejectHalt rejectHalt))
    (hMarker : c.outputTape.current = some true) :
    RunsFor program (c.resumeAt pc)
      { c.resumeAt rejectHalt with halted := true } 2 := by
  have hBranch : Step program (c.resumeAt pc) (c.resumeAt rejectHalt) := by
    simpa [Configuration.resumeAt] using
      branch_marked pc good rejectHalt (c.resumeAt pc)
        hLookup rfl rfl (by simpa [Configuration.resumeAt] using hMarker)
  exact ((RunsFor.zero _).succ hBranch).succ
    (reject_halt_step _ rfl rfl)

private theorem continue_blank (pc good : Nat) (c : Configuration)
    (hLookup : program[pc]? =
      some (.branch .output good rejectHalt rejectHalt))
    (hBlank : c.outputTape.current = none) :
    RunsFor program (c.resumeAt pc) (c.resumeAt good) 1 := by
  have hBranch : Step program (c.resumeAt pc) (c.resumeAt good) := by
    simpa [Configuration.resumeAt] using
      branch_blank pc good rejectHalt (c.resumeAt pc)
        hLookup rfl rfl (by simpa [Configuration.resumeAt] using hBlank)
  exact (RunsFor.zero _).succ hBranch

/-- Check the instance field on the actual tapes reached after the counter
rewind. The equivalence hypotheses account only for harmless outer blanks. -/
private theorem instance_check_stage (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate count false))) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 12 * count + 12 ∧
      RunsFor program
        { pc := firstRewindEnd, inputTape := input, outputTape := output }
        (target.resumeAt instanceCheckEnd) used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 17 then none else some true) ∧
      (target.pc = 17 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate count (some false) ++ [none] }) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → target.pc = 17) := by
  obtain ⟨canonical, steps, hSteps, canonicalRun, hCanonicalHalt,
    hCanonicalStatus, hCanonicalAccepted⟩ :=
      FrameWidthCheck.runs_any_loaded before count bits
  have hStart :
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate count false) } : Configuration).Equivalent
        ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    canonicalRun.exists_equivalent hStart
  have hActualHalt : actual.halted = true :=
    hEquivalent.2.1.symm.trans hCanonicalHalt
  let pre := SecurityWidthTemplate.program.asSubroutine 0 templateEnd ++
    rewindBitstring.swapTapes.asSubroutine templateEnd firstRewindEnd
  obtain ⟨used, hUsed, embedded⟩ :=
    actualRun.withSubroutine_halted pre FrameWidthCheck.program
      afterInstance instanceCheckEnd (Nat.zero_le _) rfl hActualHalt
  refine ⟨actual, used, by omega, ?_, hActualHalt, ?_, ?_, ?_⟩
  · rw [instance_check_layout]
    have hJoin :
        ({ pc := firstRewindEnd, inputTape := input,
           outputTape := output } : Configuration) =
          ({ inputTape := input, outputTape := output } : Configuration).rebasePc
            pre.length := by
      simp [pre, firstRewindEnd, templateEnd,
        Program.asSubroutine_length, Configuration.rebasePc, Nat.add_assoc]
    rw [hJoin]
    exact embedded
  · simpa [hEquivalent.1] using
      hEquivalent.2.2.2.1.symm.trans hCanonicalStatus
  · intro hPc
    obtain ⟨payload, rest, hBits, hLength, hPosition, hCounter⟩ :=
      hCanonicalAccepted (hEquivalent.1.trans hPc)
    exact ⟨payload, rest, hBits, hLength,
      hEquivalent.2.2.1.symm.trans hPosition,
      hEquivalent.2.2.2.symm.trans hCounter⟩
  · intro payload rest hBits hLength
    subst bits
    have hCanonicalPc := FrameWidthCheck.accepts_valid_loaded
      before payload rest count hLength canonicalRun hCanonicalHalt
    exact hEquivalent.1.symm.trans hCanonicalPc


/-- The first frame either takes the marked rejection exit or leaves the
same three-column counter ready for an element-width check. -/
private theorem instance_and_rewind (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate count false))) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 14 * count + 18 ∧
      RunsFor program
        { pc := firstRewindEnd, inputTape := input, outputTape := output }
        finish used ∧
      ((finish.halted = true ∧ finish.outputTape.current = some true) ∨
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          finish.pc = secondRewindEnd ∧ finish.halted = false ∧
          finish.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          finish.outputTape.Equivalent
            (Tape.ofBits (List.replicate count false))) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → finish.halted = false) := by
  obtain ⟨checked, checkedSteps, hCheckedSteps, checkRun,
    hCheckedHalt, hStatus, hAccepted, hValid⟩ :=
    instance_check_stage before count bits input output hInput hOutput
  by_cases hAccept : checked.pc = 17
  · obtain ⟨payload, rest, hBits, hLength, hPosition, hCounter⟩ :=
      hAccepted hAccept
    have hBlank : checked.outputTape.current = none := by
      simpa [hAccept] using hStatus
    have hContinue := continue_blank instanceCheckEnd secondRewindStart
      checked instance_branch_lookup hBlank
    have hCounter' : checked.outputTape.Equivalent
        ({ left := List.replicate count (some false) } : Tape) :=
      hCounter.trans (counter_outer_blank count)
    obtain ⟨rewound, rewindSteps, hRewindSteps, rewindRun,
      _, hInputRewind, hOutputRewind⟩ :=
      second_rewind_stage count checked.inputTape checked.outputTape hCounter'
    have hJoin : checked.resumeAt secondRewindStart =
        ({ pc := secondRewindStart, inputTape := checked.inputTape,
           outputTape := checked.outputTape } : Configuration) := by
      simp [Configuration.resumeAt]
    rw [← hJoin] at rewindRun
    refine ⟨rewound.resumeAt secondRewindEnd,
      checkedSteps + 1 + rewindSteps, by omega,
      (checkRun.trans hContinue).trans rewindRun, Or.inr ?_, ?_⟩
    · exact ⟨payload, rest, hBits, hLength, rfl, rfl,
        hInputRewind.trans hPosition, hOutputRewind⟩
    · intro _ _ _ _
      rfl
  · have hMarked : checked.outputTape.current = some true := by
      simpa [hAccept] using hStatus
    have hReject := reject_marked instanceCheckEnd secondRewindStart
      checked instance_branch_lookup hMarked
    refine ⟨{ checked.resumeAt rejectHalt with halted := true },
      checkedSteps + 2, by omega, checkRun.trans hReject, Or.inl ?_, ?_⟩
    · exact ⟨rfl, hMarked⟩
    · intro payload rest hBits hLength
      exact False.elim (hAccept (hValid payload rest hBits hLength))

/-- A first element frame of the expected width leaves the counter rewound
for the second element. Malformed input takes the same marked exit. -/
private theorem first_element_and_rewind (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent
      (Tape.ofBits (List.replicate (3 * count) false))) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 26 * count + 18 ∧
      RunsFor program
        { pc := secondRewindEnd, inputTape := input, outputTape := output }
        finish used ∧
      ((finish.halted = true ∧ finish.outputTape.current = some true) ∨
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          finish.pc = thirdRewindEnd ∧ finish.halted = false ∧
          finish.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          finish.outputTape.Equivalent
            (Tape.ofBits (List.replicate (3 * count) false))) ∧
      (∀ payload rest, bits = frame payload ++ rest →
        payload.length = count → finish.halted = false) := by
  obtain ⟨checked, checkedSteps, hCheckedSteps, checkRun,
    _, hStatus, hAccepted, hValid⟩ :=
    first_element_stage before count bits input output hInput hOutput
  by_cases hAccept : checked.pc = 21
  · obtain ⟨payload, rest, hBits, hLength, hPosition, hCounter⟩ :=
      hAccepted hAccept
    have hBlank : checked.outputTape.current = none := by
      simpa [hAccept] using hStatus
    have hContinue := continue_blank firstElementCheckEnd thirdRewindStart
      checked first_element_branch_lookup hBlank
    have hCounter' : checked.outputTape.Equivalent
        ({ left := List.replicate (3 * count) (some false) } : Tape) :=
      hCounter.trans (counter_outer_blank (3 * count))
    obtain ⟨rewound, rewindSteps, hRewindSteps, rewindRun,
      _, hInputRewind, hOutputRewind⟩ :=
      third_rewind_stage (3 * count) checked.inputTape checked.outputTape hCounter'
    have hJoin : checked.resumeAt thirdRewindStart =
        ({ pc := thirdRewindStart, inputTape := checked.inputTape,
           outputTape := checked.outputTape } : Configuration) := by
      simp [Configuration.resumeAt]
    rw [← hJoin] at rewindRun
    refine ⟨rewound.resumeAt thirdRewindEnd,
      checkedSteps + 1 + rewindSteps, by omega,
      (checkRun.trans hContinue).trans rewindRun, Or.inr ?_, ?_⟩
    · exact ⟨payload, rest, hBits, hLength, rfl, rfl,
        hInputRewind.trans hPosition, hOutputRewind⟩
    · intro _ _ _ _
      rfl
  · have hMarked : checked.outputTape.current = some true := by
      simpa [hAccept] using hStatus
    have hReject := reject_marked firstElementCheckEnd thirdRewindStart
      checked first_element_branch_lookup hMarked
    refine ⟨{ checked.resumeAt rejectHalt with halted := true },
      checkedSteps + 2, by omega, checkRun.trans hReject, Or.inl ?_, ?_⟩
    · exact ⟨rfl, hMarked⟩
    · intro payload rest hBits hLength
      exact False.elim (hAccept (hValid payload rest hBits hLength))

theorem erase_counter_embedded (pre suffix : Program)
    (returnPc count : Nat) (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) ++ [none] } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 4 * count + 3 ∧
      RunsFor (Program.withSubroutine pre eraseOutputBlock suffix returnPc)
        { pc := pre.length, inputTape := input, outputTape := output }
        (target.resumeAt returnPc) used ∧
      target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent ({} : Tape) := by
  let canonicalStart := eraseOutputBlockStart input [] (List.replicate count false) []
  let canonicalFinish := eraseOutputBlockFinish input [] (List.replicate count false) []
  have hCanonical : RunsFor eraseOutputBlock canonicalStart canonicalFinish
      (4 * count + 3) := by
    simpa [canonicalStart, canonicalFinish] using
      eraseOutputBlock_runs input [] (List.replicate count false) []
  have hStart : canonicalStart.Equivalent
      ({ inputTape := input, outputTape := output } : Configuration) := by
    have hCanonicalStart : canonicalStart =
        ({ inputTape := input,
           outputTape := { left := List.replicate count (some false) ++ [none] } } : Configuration) := by
      exact eraseOutputBlockStart_replicate input count
    rw [hCanonicalStart]
    exact ⟨rfl, rfl, Tape.Equivalent.refl _, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    hCanonical.exists_equivalent hStart
  have hHalt : actual.halted = true := by
    exact hEquivalent.2.1.symm.trans (by rfl)
  obtain ⟨used, hUsed, embedded⟩ :=
    actualRun.withSubroutine_halted pre eraseOutputBlock suffix
      returnPc (Nat.zero_le _) rfl hHalt
  refine ⟨actual, used, hUsed,
    by simpa [Configuration.rebasePc] using embedded,
    hHalt, ?_, ?_⟩
  · have hCanonicalInput : canonicalFinish.inputTape = input := by
      rw [show canonicalFinish =
        { pc := 4, inputTape := input,
          outputTape := { right := List.replicate (count + 1) none },
          halted := true } from eraseOutputBlockFinish_replicate input count]
    exact hEquivalent.2.2.1.symm.trans
      (by rw [hCanonicalInput]; exact Tape.Equivalent.refl _)
  · have hBlank : canonicalFinish.outputTape.Equivalent ({} : Tape) := by
      rw [show canonicalFinish =
        { pc := 4, inputTape := input,
          outputTape := { right := List.replicate (count + 1) none },
          halted := true } from eraseOutputBlockFinish_replicate input count]
      exact Tape.blank_padding_equivalent [] (count + 1)
    exact hEquivalent.2.2.2.symm.trans hBlank

private theorem tail_branch_lookup :
    program[tailCheck]? =
      some (.branch .input eraseStart rejectWrite rejectWrite) := by
  native_decide

private theorem reject_write_lookup :
    program[rejectWrite]? = some (.write .output true) := by
  native_decide

private theorem reject_jump_lookup :
    program[rejectWrite + 1]? = some (.jump rejectHalt) := by
  native_decide

private def beforeErase : Program :=
  beforeSecondElementCheck ++
    FrameWidthCheckThree.program.asSubroutine thirdRewindEnd secondElementCheckEnd ++
    [.branch .output tailCheck rejectHalt rejectHalt,
     .branch .input eraseStart rejectWrite rejectWrite]

private theorem beforeErase_length : beforeErase.length = eraseStart := by
  simp [beforeErase, beforeSecondElementCheck_length, eraseStart,
    tailCheck, secondElementCheckEnd, Program.asSubroutine_length,
    Nat.add_assoc]

private theorem erase_layout : program =
    Program.withSubroutine beforeErase eraseOutputBlock afterErase eraseEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, afterFirstElement, afterThirdRewind,
    afterSecondElement, Program.withSubroutine]
  rw [beforeErase_length]
  simp [beforeErase, beforeSecondElementCheck, beforeThirdRewind,
    beforeFirstElementCheck, beforeSecondRewind, List.append_assoc]

private theorem erase_stage (count : Nat) (input output : Tape)
    (hOutput : output.Equivalent
      ({ left := List.replicate count (some false) ++ [none] } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 4 * count + 3 ∧
      RunsFor program
        { pc := eraseStart, inputTape := input, outputTape := output }
        (target.resumeAt eraseEnd) used ∧
      target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent ({} : Tape) := by
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hBlank⟩ :=
    erase_counter_embedded beforeErase afterErase eraseEnd count
      input output hOutput
  refine ⟨target, used, hUsed, ?_, hHalt, hInput, hBlank⟩
  rw [erase_layout]
  simpa only [beforeErase_length] using run

theorem rewind_input_embedded (pre suffix : Program)
    (returnPc : Nat) (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent
      ({ left := bits.reverse.map some } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * bits.length + 4 ∧
      RunsFor (Program.withSubroutine pre rewindBitstring suffix returnPc)
        { pc := pre.length, inputTape := input, outputTape := output }
        (target.resumeAt returnPc) used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits bits) ∧
      target.outputTape.Equivalent output := by
  let canonicalStart := rewindBitstringStart bits output
  let canonicalFinish := rewindBitstringFinish bits output
  have hCanonical : RunsFor rewindBitstring canonicalStart canonicalFinish
      (2 * bits.length + 4) := rewindBitstring_runs bits output
  have hStart : canonicalStart.Equivalent
      ({ inputTape := input, outputTape := output } : Configuration) := by
    exact ⟨rfl, rfl, hInput.symm, Tape.Equivalent.refl _⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    hCanonical.exists_equivalent hStart
  have hHalt : actual.halted = true := hEquivalent.2.1.symm.trans (by rfl)
  obtain ⟨used, hUsed, embedded⟩ :=
    actualRun.withSubroutine_halted pre rewindBitstring suffix returnPc
      (Nat.zero_le _) rfl hHalt
  refine ⟨actual, used, hUsed,
    by simpa [Configuration.rebasePc] using embedded,
    hHalt, ?_, ?_⟩
  · exact hEquivalent.2.2.1.symm.trans
      (rewindBitstringFinish_input_equivalent bits output)
  · exact hEquivalent.2.2.2.symm.trans (Tape.Equivalent.refl _)

private def beforeInputRewind : Program :=
  beforeErase ++ eraseOutputBlock.asSubroutine eraseStart eraseEnd

private theorem beforeInputRewind_length :
    beforeInputRewind.length = eraseEnd := by
  simp [beforeInputRewind, beforeErase_length, eraseEnd,
    Program.asSubroutine_length, Nat.add_assoc]

private theorem input_rewind_layout : program =
    Program.withSubroutine beforeInputRewind rewindBitstring
      finishCode inputRewindEnd := by
  simp only [program, postTemplate, afterFirstRewind, afterInstance,
    afterSecondRewind, afterFirstElement, afterThirdRewind,
    afterSecondElement, afterErase, Program.withSubroutine]
  rw [beforeInputRewind_length]
  simp [beforeInputRewind, beforeErase, beforeSecondElementCheck,
    beforeThirdRewind, beforeFirstElementCheck, beforeSecondRewind,
    List.append_assoc]

private theorem input_rewind_stage (bits : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent
      ({ left := bits.reverse.map some } : Tape)) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 2 * bits.length + 4 ∧
      RunsFor program
        { pc := eraseEnd, inputTape := input, outputTape := output }
        (target.resumeAt inputRewindEnd) used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits bits) ∧
      target.outputTape.Equivalent output := by
  obtain ⟨target, used, hUsed, run, hHalt, hPosition, hOutput⟩ :=
    rewind_input_embedded beforeInputRewind finishCode inputRewindEnd
      bits input output hInput
  refine ⟨target, used, hUsed, ?_, hHalt, hPosition, hOutput⟩
  rw [input_rewind_layout]
  simpa only [beforeInputRewind_length] using run

private theorem success_halt_lookup : program[inputRewindEnd]? = some .halt := by
  native_decide

private theorem success_halt_step (c : Configuration)
    (hPc : c.pc = inputRewindEnd) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  simp [Step, successors, next, hPc, hActive, success_halt_lookup,
    Instruction.next]

private theorem frame_history (bits : List Bool) :
    (frame bits).reverse.map some =
      bits.reverse.map some ++ some false ::
        List.replicate bits.length (some true) := by
  simp [frame, List.reverse_append, List.map_append,
    List.append_assoc]

theorem frame_append_unique (count : Nat)
    (first second firstRest secondRest : List Bool)
    (hFirst : first.length = count) (hSecond : second.length = count)
    (h : frame first ++ firstRest = frame second ++ secondRest) :
    first = second ∧ firstRest = secondRest := by
  have hPayload : first ++ firstRest = second ++ secondRest := by
    simpa [frame, hFirst, hSecond, List.append_assoc] using h
  have hFirstEq : first = second := by
    have hTake := congrArg (List.take count) hPayload
    simpa [hFirst, hSecond] using hTake
  constructor
  · exact hFirstEq
  · subst second
    exact List.append_cancel_left hPayload

private def finalHistory (n : Nat)
    (instanceBits first second : List Bool) : List (Option Bool) :=
  second.reverse.map some ++
    some false :: List.replicate second.length (some true) ++
  first.reverse.map some ++
    some false :: List.replicate first.length (some true) ++
  instanceBits.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++
  some false :: List.replicate n (some true)

private theorem request_history (n : Nat) (instanceBits first second : List Bool) :
    (encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second).reverse.map some =
      finalHistory n instanceBits first second := by
  simp only [List.reverse_append, List.map_append]
  rw [frame_history, frame_history, frame_history]
  simp [encodeSecurityParameter, finalHistory, List.append_assoc]

private theorem configuration_at (c : Configuration) (pc : Nat)
    (hPc : c.pc = pc) (hRunning : c.halted = false) :
    c = { pc := pc, inputTape := c.inputTape, outputTape := c.outputTape } := by
  cases c
  simp_all

private theorem resumeAt_self (c : Configuration) (pc : Nat)
    (hPc : c.pc = pc) (hRunning : c.halted = false) :
    c.resumeAt pc = c := by
  cases c
  simp_all [Configuration.resumeAt]

private theorem tail_blank_step (c : Configuration)
    (hBlank : c.inputTape.current = none) :
    Step program (c.resumeAt tailCheck) (c.resumeAt eraseStart) := by
  simp [Step, successors, next, tail_branch_lookup,
    Configuration.resumeAt, Configuration.tape, hBlank, Instruction.next]

private theorem tail_nonblank_step (c : Configuration) (bit : Bool)
    (hBit : c.inputTape.current = some bit) :
    Step program (c.resumeAt tailCheck) (c.resumeAt rejectWrite) := by
  cases bit <;>
    simp [Step, successors, next, tail_branch_lookup,
      Configuration.resumeAt, Configuration.tape, hBit, Instruction.next]

private theorem tail_reject (c : Configuration) (bit : Bool)
    (hBit : c.inputTape.current = some bit) :
    RunsFor program (c.resumeAt tailCheck)
      { c.resumeAt rejectHalt with
        outputTape := c.outputTape.write (some true), halted := true } 4 := by
  let selected := c.resumeAt rejectWrite
  let marked : Configuration :=
    { pc := rejectWrite + 1, inputTape := c.inputTape,
      outputTape := c.outputTape.write (some true) }
  let jumped : Configuration := { marked with pc := rejectHalt }
  have hBranch : Step program (c.resumeAt tailCheck) selected :=
    tail_nonblank_step c bit hBit
  have hWrite : Step program selected marked := by
    simp [Step, successors, next, reject_write_lookup,
      selected, marked, Configuration.resumeAt,
      Configuration.updateTape, Configuration.advance, Instruction.next]
  have hJump : Step program marked jumped := by
    simp [Step, successors, next, reject_jump_lookup,
      marked, jumped, Instruction.next]
  have hHalt : Step program jumped
      { c.resumeAt rejectHalt with
        outputTape := c.outputTape.write (some true), halted := true } := by
    simpa [jumped, marked, selected, Configuration.resumeAt] using
      reject_halt_step jumped rfl rfl
  exact ((((RunsFor.zero _).succ hBranch).succ hWrite).succ hJump).succ hHalt

private def AcceptedScan (raw : List Bool) (finish : Configuration) : Prop :=
  ∃ (n : Nat) (instanceBits first second tail : List Bool),
    raw = encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second ++ tail ∧
    instanceBits.length = 3 * (n + 3) ∧
    first.length = n + 3 ∧ second.length = n + 3 ∧
    finish.pc = secondElementCheckEnd ∧ finish.halted = false ∧
    finish.inputTape.Equivalent
      { Tape.ofBits tail with left := finalHistory n instanceBits first second } ∧
    finish.outputTape.Equivalent
      { left := List.replicate (3 * (n + 3)) (some false) ++ [none] } ∧
    finish.outputTape.current = none

/-- The concrete verifier reaches the final element boundary only after all
three advertised widths match the security prefix. Every other finite input
takes a marked, halted rejection branch. -/
private theorem scan_all (raw : List Bool) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 200 * (raw.length + 1) + 1000 ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      ((finish.halted = true ∧ finish.outputTape.current = some true) ∨
        AcceptedScan raw finish) := by
  obtain ⟨templ, templateSteps, width, rest, before,
    hTemplateSteps, hWidth, templateRun, _, hTemplateInput,
    hTemplateOutput, _, hPrefix⟩ := template_stage raw
  obtain ⟨rewound, rewindSteps, hRewindSteps, rewindRun,
    _, hRewoundInput, hRewoundOutput⟩ :=
      first_rewind_stage (3 * width) templ.inputTape
  have hJoinTemplate : templ.resumeAt templateEnd =
      ({ pc := templateEnd, inputTape := templ.inputTape,
         outputTape := { left := List.replicate (3 * width) (some false) } } : Configuration) := by
    simp [Configuration.resumeAt, hTemplateOutput]
  rw [← hJoinTemplate] at rewindRun
  have hStartInput : rewound.inputTape.Equivalent
      { Tape.ofBits rest with left := before } := by
    rw [hRewoundInput, hTemplateInput]
    exact Tape.Equivalent.refl _
  obtain ⟨afterInstance, instanceSteps, hInstanceSteps,
    instanceRun, instanceOutcome, _⟩ :=
      instance_and_rewind before (3 * width) rest
        rewound.inputTape rewound.outputTape hStartInput hRewoundOutput
  have hJoinRewound : rewound.resumeAt firstRewindEnd =
      ({ pc := firstRewindEnd, inputTape := rewound.inputTape,
         outputTape := rewound.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoinRewound] at instanceRun
  have firstRun : RunsFor program (Configuration.initial raw) afterInstance
      (templateSteps + rewindSteps + instanceSteps) :=
    (templateRun.trans rewindRun).trans instanceRun
  rcases instanceOutcome with rejected | ⟨instanceBits, rest₁,
      hInstanceBits, hInstanceLength, hInstancePc, hInstanceActive,
      hInstanceInput, hInstanceCounter⟩
  · refine ⟨afterInstance, templateSteps + rewindSteps + instanceSteps,
      by omega, firstRun, Or.inl rejected⟩
  have hRestNonempty : rest ≠ [] := by
    rw [hInstanceBits]
    simp [frame]
  obtain ⟨n, hRawPrefix, hWidthN, hBefore⟩ := hPrefix hRestNonempty
  let beforeFirst : List (Option Bool) :=
    instanceBits.reverse.map some ++
      some false :: List.replicate (3 * width) (some true) ++ before
  obtain ⟨afterFirst, firstSteps, hFirstSteps,
    firstElementRun, firstOutcome, _⟩ :=
      first_element_and_rewind beforeFirst width rest₁
        afterInstance.inputTape afterInstance.outputTape
        hInstanceInput hInstanceCounter
  have hJoinInstance : afterInstance =
      ({ pc := secondRewindEnd, inputTape := afterInstance.inputTape,
         outputTape := afterInstance.outputTape } : Configuration) :=
    configuration_at afterInstance secondRewindEnd hInstancePc hInstanceActive
  rw [← hJoinInstance] at firstElementRun
  have secondRun : RunsFor program (Configuration.initial raw) afterFirst
      (templateSteps + rewindSteps + instanceSteps + firstSteps) :=
    firstRun.trans firstElementRun
  rcases firstOutcome with rejected | ⟨first, rest₂,
      hFirstBits, hFirstLength, hFirstPc, hFirstActive,
      hFirstInput, hFirstCounter⟩
  · refine ⟨afterFirst, templateSteps + rewindSteps + instanceSteps + firstSteps,
      by omega, secondRun, Or.inl rejected⟩
  let beforeSecond : List (Option Bool) :=
    first.reverse.map some ++
      some false :: List.replicate width (some true) ++ beforeFirst
  obtain ⟨checked, secondSteps, hSecondSteps, secondElementRun,
    _, hSecondStatus, hSecondAccepted, hSecondValid⟩ :=
      second_element_stage beforeSecond width rest₂
        afterFirst.inputTape afterFirst.outputTape hFirstInput hFirstCounter
  have hJoinFirst : afterFirst =
      ({ pc := thirdRewindEnd, inputTape := afterFirst.inputTape,
         outputTape := afterFirst.outputTape } : Configuration) :=
    configuration_at afterFirst thirdRewindEnd hFirstPc hFirstActive
  rw [← hJoinFirst] at secondElementRun
  have thirdRun : RunsFor program (Configuration.initial raw)
      (checked.resumeAt secondElementCheckEnd)
      (templateSteps + rewindSteps + instanceSteps + firstSteps + secondSteps) :=
    secondRun.trans secondElementRun
  by_cases hAccept : checked.pc = 21
  · obtain ⟨second, tail, hSecondBits, hSecondLength,
      hSecondInput, hSecondCounter⟩ := hSecondAccepted hAccept
    have hBlank : checked.outputTape.current = none := by
      simpa [hAccept] using hSecondStatus
    have hRaw : raw = encodeSecurityParameter n ++ frame instanceBits ++
        frame first ++ frame second ++ tail := by
      simp [hRawPrefix, hInstanceBits, hFirstBits, hSecondBits,
        List.append_assoc]
    have hHistory : checked.inputTape.Equivalent
        { Tape.ofBits tail with left := finalHistory n instanceBits first second } := by
      simpa [beforeSecond, beforeFirst, finalHistory,
        hBefore, hWidthN, hInstanceLength,
        hFirstLength, hSecondLength, List.append_assoc] using hSecondInput
    have hCounter : checked.outputTape.Equivalent
        ({ left := List.replicate (3 * (n + 3)) (some false) ++ [none] } : Tape) := by
      simpa [hWidthN] using hSecondCounter
    refine ⟨checked.resumeAt secondElementCheckEnd,
      templateSteps + rewindSteps + instanceSteps + firstSteps + secondSteps,
      by omega, thirdRun, Or.inr ?_⟩
    exact ⟨n, instanceBits, first, second, tail, hRaw,
      by omega, by omega, by omega, rfl, rfl,
      hHistory, hCounter, hBlank⟩
  · have hMarked : checked.outputTape.current = some true := by
      simpa [hAccept] using hSecondStatus
    have hReject := reject_marked secondElementCheckEnd tailCheck
      checked second_element_branch_lookup hMarked
    refine ⟨{ checked.resumeAt rejectHalt with halted := true },
      templateSteps + rewindSteps + instanceSteps + firstSteps + secondSteps + 2,
      by omega, thirdRun.trans hReject, Or.inl ?_⟩
    exact ⟨rfl, hMarked⟩

/-- Every finite request either rejects with a visible marker or is restored
to its original raw input for the framed multiplier. No abstract parser or
free tape reset occurs in this trace. -/
theorem runs_any (raw : List Bool) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 300 * (raw.length + 1) + 2000 ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      ((finish.outputTape.current = some true) ∨
        (finish.pc = inputRewindEnd ∧
          finish.inputTape.Equivalent (Tape.ofBits raw) ∧
          finish.outputTape.Equivalent ({} : Tape) ∧
          ∃ n instanceBits first second,
            raw = encodeSecurityParameter n ++ frame instanceBits ++
              frame first ++ frame second ∧
            instanceBits.length = 3 * (n + 3) ∧
            first.length = n + 3 ∧ second.length = n + 3)) := by
  obtain ⟨scanned, scanSteps, hScanSteps, scanRun, outcome⟩ := scan_all raw
  rcases outcome with rejected | ⟨n, instanceBits, first, second, tail,
      hRaw, hInstanceLength, hFirstLength, hSecondLength,
      hPc, hActive, hInput, hCounter, hBlank⟩
  · exact ⟨scanned, scanSteps, by omega, scanRun,
      rejected.1, Or.inl rejected.2⟩
  have hResume : scanned.resumeAt secondElementCheckEnd = scanned :=
    resumeAt_self scanned secondElementCheckEnd hPc hActive
  have hOutputBranch := continue_blank secondElementCheckEnd tailCheck
    scanned second_element_branch_lookup hBlank
  rw [hResume] at hOutputBranch
  cases tail with
  | cons bit tail =>
      have hCurrent : scanned.inputTape.current = some bit := by
        exact hInput.1
      have hReject := tail_reject scanned bit hCurrent
      refine ⟨{ scanned.resumeAt rejectHalt with
        outputTape := scanned.outputTape.write (some true), halted := true },
        scanSteps + 1 + 4, by omega,
        (scanRun.trans hOutputBranch).trans hReject, rfl, Or.inl ?_⟩
      rfl
  | nil =>
      have hRaw0 : raw = encodeSecurityParameter n ++ frame instanceBits ++
          frame first ++ frame second := by
        simpa using hRaw
      have hCurrent : scanned.inputTape.current = none := hInput.1
      have hTailStep := tail_blank_step scanned hCurrent
      have hReady : RunsFor program (Configuration.initial raw)
          (scanned.resumeAt eraseStart) (scanSteps + 2) :=
        (scanRun.trans hOutputBranch).succ hTailStep
      obtain ⟨erased, eraseSteps, hEraseSteps, eraseRun,
        _, hEraseInput, hEraseOutput⟩ :=
        erase_stage (3 * (n + 3)) scanned.inputTape scanned.outputTape hCounter
      have hJoinErase : scanned.resumeAt eraseStart =
          ({ pc := eraseStart, inputTape := scanned.inputTape,
             outputTape := scanned.outputTape } : Configuration) := by
        simp [Configuration.resumeAt]
      rw [← hJoinErase] at eraseRun
      have hRawHistory : scanned.inputTape.Equivalent
          ({ left := raw.reverse.map some } : Tape) := by
        rw [hRaw0, request_history]
        simpa [Tape.ofBits] using hInput
      have hErasedHistory : erased.inputTape.Equivalent
          ({ left := raw.reverse.map some } : Tape) :=
        hEraseInput.trans hRawHistory
      obtain ⟨rewound, rewindSteps, hRewindSteps, rewindRun,
        _, hRewindInput, hRewindOutput⟩ :=
        input_rewind_stage raw erased.inputTape erased.outputTape hErasedHistory
      have hJoinRewind : erased.resumeAt eraseEnd =
          ({ pc := eraseEnd, inputTape := erased.inputTape,
             outputTape := erased.outputTape } : Configuration) := by
        simp [Configuration.resumeAt]
      rw [← hJoinRewind] at rewindRun
      have hStop := success_halt_step (rewound.resumeAt inputRewindEnd) rfl rfl
      have hWidthBound : n + 3 ≤ raw.length + 3 := by
        rw [hRaw0]
        simp [frame, encodeSecurityParameter]
      refine ⟨{ rewound.resumeAt inputRewindEnd with halted := true },
        scanSteps + 2 + eraseSteps + rewindSteps + 1,
        by omega,
        (((hReady.trans eraseRun).trans rewindRun).succ hStop),
        rfl, Or.inr ?_⟩
      exact ⟨rfl, hRewindInput,
        hRewindOutput.trans hEraseOutput,
        ⟨n, instanceBits, first, second, hRaw0,
          hInstanceLength, hFirstLength, hSecondLength⟩⟩

/-- Correctly sized request frames take the accepting branch. The result
uses the actual verifier trace, including erasure and input rewind. -/
theorem runs_valid (n : Nat) (instanceBits first second : List Bool)
    (hInstance : instanceBits.length = 3 * (n + 3))
    (hFirst : first.length = n + 3)
    (hSecond : second.length = n + 3) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ frame second
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 300 * (raw.length + 1) + 2000 ∧
      RunsFor program (Configuration.initial raw) finish used ∧
      finish.halted = true ∧ finish.pc = inputRewindEnd ∧
      finish.inputTape.Equivalent (Tape.ofBits raw) ∧
      finish.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++
    frame first ++ frame second
  let rest₀ := frame instanceBits ++ frame first ++ frame second
  obtain ⟨templ, templateSteps, hTemplateSteps, templateRun,
    hTemplateInput, hTemplateOutput⟩ := template_valid_stage n rest₀
  obtain ⟨rewound, rewindSteps, hRewindSteps, rewindRun,
    _, hRewoundInput, hRewoundOutput⟩ :=
      first_rewind_stage (3 * (n + 3)) templ.inputTape
  have hJoinTemplate : templ.resumeAt templateEnd =
      ({ pc := templateEnd, inputTape := templ.inputTape,
         outputTape := { left := List.replicate (3 * (n + 3)) (some false) } } : Configuration) := by
    simp [Configuration.resumeAt, hTemplateOutput]
  rw [← hJoinTemplate] at rewindRun
  let before₀ : List (Option Bool) :=
    some false :: List.replicate n (some true)
  have hStartInput : rewound.inputTape.Equivalent
      { Tape.ofBits rest₀ with left := before₀ } := by
    rw [hRewoundInput, hTemplateInput]
    exact Tape.Equivalent.refl _
  obtain ⟨afterInstance, instanceSteps, hInstanceSteps,
    instanceRun, instanceOutcome, hInstanceValid⟩ :=
      instance_and_rewind before₀ (3 * (n + 3)) rest₀
        rewound.inputTape rewound.outputTape hStartInput hRewoundOutput
  have hJoinRewound : rewound.resumeAt firstRewindEnd =
      ({ pc := firstRewindEnd, inputTape := rewound.inputTape,
         outputTape := rewound.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoinRewound] at instanceRun
  have firstRun : RunsFor program (Configuration.initial raw) afterInstance
      (templateSteps + rewindSteps + instanceSteps) := by
    simpa only [raw, rest₀, List.append_assoc] using
      (templateRun.trans rewindRun).trans instanceRun
  have hInstanceActive : afterInstance.halted = false :=
    hInstanceValid instanceBits (frame first ++ frame second)
      (by simp [rest₀, List.append_assoc]) hInstance
  rcases instanceOutcome with rejected | ⟨decodedInstance, rest₁,
      hInstanceBits, hDecodedLength, hInstancePc, _,
      hInstanceInput, hInstanceCounter⟩
  · simp [hInstanceActive] at rejected
  obtain ⟨hDecodedInstance, hRest₁⟩ :=
    frame_append_unique (3 * (n + 3)) instanceBits decodedInstance
      (frame first ++ frame second) rest₁ hInstance hDecodedLength
      (by simpa only [rest₀, List.append_assoc] using hInstanceBits)
  subst decodedInstance
  subst rest₁
  let beforeFirst : List (Option Bool) :=
    instanceBits.reverse.map some ++
      some false :: List.replicate (3 * (n + 3)) (some true) ++ before₀
  obtain ⟨afterFirst, firstSteps, hFirstSteps,
    firstElementRun, firstOutcome, hFirstValid⟩ :=
      first_element_and_rewind beforeFirst (n + 3)
        (frame first ++ frame second)
        afterInstance.inputTape afterInstance.outputTape
        hInstanceInput hInstanceCounter
  have hJoinInstance : afterInstance =
      ({ pc := secondRewindEnd, inputTape := afterInstance.inputTape,
         outputTape := afterInstance.outputTape } : Configuration) :=
    configuration_at afterInstance secondRewindEnd hInstancePc hInstanceActive
  rw [← hJoinInstance] at firstElementRun
  have secondRun : RunsFor program (Configuration.initial raw) afterFirst
      (templateSteps + rewindSteps + instanceSteps + firstSteps) :=
    firstRun.trans firstElementRun
  have hFirstActive : afterFirst.halted = false :=
    hFirstValid first (frame second) rfl hFirst
  rcases firstOutcome with rejected | ⟨decodedFirst, rest₂,
      hFirstBits, hDecodedFirstLength, hFirstPc, _,
      hFirstInput, hFirstCounter⟩
  · simp [hFirstActive] at rejected
  obtain ⟨hDecodedFirst, hRest₂⟩ :=
    frame_append_unique (n + 3) first decodedFirst (frame second) rest₂
      hFirst hDecodedFirstLength hFirstBits
  subst decodedFirst
  subst rest₂
  let beforeSecond : List (Option Bool) :=
    first.reverse.map some ++
      some false :: List.replicate (n + 3) (some true) ++ beforeFirst
  obtain ⟨checked, secondSteps, hSecondSteps, secondElementRun,
    _, hSecondStatus, hSecondAccepted, hSecondValid⟩ :=
      second_element_stage beforeSecond (n + 3) (frame second)
        afterFirst.inputTape afterFirst.outputTape hFirstInput hFirstCounter
  have hJoinFirst : afterFirst =
      ({ pc := thirdRewindEnd, inputTape := afterFirst.inputTape,
         outputTape := afterFirst.outputTape } : Configuration) :=
    configuration_at afterFirst thirdRewindEnd hFirstPc hFirstActive
  rw [← hJoinFirst] at secondElementRun
  have thirdRun : RunsFor program (Configuration.initial raw)
      (checked.resumeAt secondElementCheckEnd)
      (templateSteps + rewindSteps + instanceSteps + firstSteps + secondSteps) :=
    secondRun.trans secondElementRun
  have hAccept : checked.pc = 21 := hSecondValid second [] (by simp) hSecond
  obtain ⟨decodedSecond, tail, hSecondBits, hDecodedSecondLength,
    hSecondInput, hSecondCounter⟩ := hSecondAccepted hAccept
  obtain ⟨hDecodedSecond, hTail⟩ :=
    frame_append_unique (n + 3) second decodedSecond [] tail
      hSecond hDecodedSecondLength (by simpa using hSecondBits)
  subst decodedSecond
  subst tail
  have hBlank : checked.outputTape.current = none := by
    simpa [hAccept] using hSecondStatus
  have hOutputBranch := continue_blank secondElementCheckEnd tailCheck
    checked second_element_branch_lookup hBlank
  have hCurrent : checked.inputTape.current = none := hSecondInput.1
  have hTailStep := tail_blank_step checked hCurrent
  have hReady : RunsFor program (Configuration.initial raw)
      (checked.resumeAt eraseStart)
      (templateSteps + rewindSteps + instanceSteps + firstSteps + secondSteps + 2) :=
    (thirdRun.trans hOutputBranch).succ hTailStep
  have hCounter : checked.outputTape.Equivalent
      ({ left := List.replicate (3 * (n + 3)) (some false) ++ [none] } : Tape) :=
    hSecondCounter
  obtain ⟨erased, eraseSteps, hEraseSteps, eraseRun,
    _, hEraseInput, hEraseOutput⟩ :=
    erase_stage (3 * (n + 3)) checked.inputTape checked.outputTape hCounter
  have hJoinErase : checked.resumeAt eraseStart =
      ({ pc := eraseStart, inputTape := checked.inputTape,
         outputTape := checked.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoinErase] at eraseRun
  have hRawHistory : checked.inputTape.Equivalent
      ({ left := raw.reverse.map some } : Tape) := by
    have hHist : raw.reverse.map some =
        finalHistory n instanceBits first second := by
      exact request_history n instanceBits first second
    rw [hHist]
    simpa [beforeSecond, beforeFirst, before₀, finalHistory,
      hInstance, hFirst, hSecond, List.append_assoc, Tape.ofBits]
      using hSecondInput
  have hErasedHistory : erased.inputTape.Equivalent
      ({ left := raw.reverse.map some } : Tape) :=
    hEraseInput.trans hRawHistory
  obtain ⟨rewoundFinal, finalRewindSteps, hFinalRewindSteps,
    finalRewindRun, _, hRewindInput, hRewindOutput⟩ :=
    input_rewind_stage raw erased.inputTape erased.outputTape hErasedHistory
  have hJoinRewind : erased.resumeAt eraseEnd =
      ({ pc := eraseEnd, inputTape := erased.inputTape,
         outputTape := erased.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoinRewind] at finalRewindRun
  have hStop := success_halt_step
    (rewoundFinal.resumeAt inputRewindEnd) rfl rfl
  refine ⟨{ rewoundFinal.resumeAt inputRewindEnd with halted := true },
    templateSteps + rewindSteps + instanceSteps + firstSteps +
      secondSteps + 2 + eraseSteps + finalRewindSteps + 1,
    ?_, ?_, rfl, rfl, hRewindInput,
    hRewindOutput.trans hEraseOutput⟩
  · have hRawLength : raw.length = 11 * n + 34 := by
      simp [raw, frame, encodeSecurityParameter, hInstance, hFirst, hSecond]
      omega
    have hRawLength' :
        (encodeSecurityParameter n ++ frame instanceBits ++
          frame first ++ frame second).length = 11 * n + 34 := by
      simpa only [raw] using hRawLength
    omega
  · exact (((hReady.trans eraseRun).trans finalRewindRun).succ hStop)

def budget (length : Nat) : Nat := 300 * (length + 1) + 2000

theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  change PolynomiallyBounded (fun n => 300 * (n + 1) + 2000)
  exact ((PolynomiallyBounded.const 300).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 2000)

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt, _⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩


end Machine.FramedProductGuard
