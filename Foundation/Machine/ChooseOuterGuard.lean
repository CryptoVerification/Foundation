import Foundation.Machine.CompleteFrameCheck
import Foundation.Machine.FramedProductGuard

namespace Machine.ChooseOuterGuard

private def templateEnd : Nat := SecurityWidthTemplate.program.length + 1
private def instanceStart : Nat := templateEnd + rewindBitstring.swapTapes.length + 1
private def instanceEnd : Nat := instanceStart + FrameWidthCheck.program.length + 1
private def eraseStart : Nat := instanceEnd + 1
private def frameStart : Nat := eraseStart + eraseOutputBlock.length + 1
private def frameEnd : Nat := frameStart + CompleteFrameCheck.program.length + 1
private def inputRewindStart : Nat := frameEnd + 1
private def acceptPc : Nat := inputRewindStart + rewindBitstring.length + 1
private def rejectPc : Nat := acceptPc + 1

private def preInstance : Program :=
  SecurityWidthTemplate.program.asSubroutine 0 templateEnd ++
    rewindBitstring.swapTapes.asSubroutine templateEnd instanceStart
private def preErase : Program := preInstance ++
  FrameWidthCheck.program.asSubroutine instanceStart instanceEnd ++
    [.branch .output eraseStart rejectPc rejectPc]
private def preFrame : Program := preErase ++ eraseOutputBlock.asSubroutine eraseStart frameStart
private def preInputRewind : Program := preFrame ++
  CompleteFrameCheck.program.asSubroutine frameStart frameEnd ++
    [.branch .output inputRewindStart rejectPc rejectPc]

/-- Check a unary security prefix, the actual `3*(n+3)`-bit instance frame,
and exactly one complete response frame. Acceptance physically clears the
counter and restores the original request for the validation body. Rejection
halts immediately with a visible marker; no decoder is a machine opcode. -/
def program : Program := preInputRewind ++
  rewindBitstring.asSubroutine inputRewindStart acceptPc ++ [.halt, .halt]

private def afterInstance : Program :=
  [.branch .output eraseStart rejectPc rejectPc] ++
    eraseOutputBlock.asSubroutine eraseStart frameStart ++
    CompleteFrameCheck.program.asSubroutine frameStart frameEnd ++
    [.branch .output inputRewindStart rejectPc rejectPc] ++
    rewindBitstring.asSubroutine inputRewindStart acceptPc ++ [.halt, .halt]
private def afterFrame : Program :=
  [.branch .output inputRewindStart rejectPc rejectPc] ++
    rewindBitstring.asSubroutine inputRewindStart acceptPc ++ [.halt, .halt]
private def afterErase : Program :=
  CompleteFrameCheck.program.asSubroutine frameStart frameEnd ++ afterFrame
private def afterTemplate : Program :=
  rewindBitstring.swapTapes.asSubroutine templateEnd instanceStart ++
    FrameWidthCheck.program.asSubroutine instanceStart instanceEnd ++ afterInstance

private theorem template_layout : program =
    Program.withSubroutine [] SecurityWidthTemplate.program afterTemplate templateEnd := by native_decide
private theorem rewind_layout : program = Program.withSubroutine
    (SecurityWidthTemplate.program.asSubroutine 0 templateEnd) rewindBitstring.swapTapes
    (FrameWidthCheck.program.asSubroutine instanceStart instanceEnd ++ afterInstance) instanceStart := by native_decide
private theorem instance_layout : program =
    Program.withSubroutine preInstance FrameWidthCheck.program afterInstance instanceEnd := by native_decide
private theorem erase_layout : program =
    Program.withSubroutine preErase eraseOutputBlock afterErase frameStart := by native_decide
private theorem frame_layout : program =
    Program.withSubroutine preFrame CompleteFrameCheck.program afterFrame frameEnd := by native_decide
private theorem input_rewind_layout : program =
    Program.withSubroutine preInputRewind rewindBitstring [.halt, .halt] acceptPc := by native_decide

private theorem preInstance_length : preInstance.length = instanceStart := by native_decide
private theorem preErase_length : preErase.length = eraseStart := by native_decide
private theorem preFrame_length : preFrame.length = frameStart := by native_decide
private theorem preInputRewind_length : preInputRewind.length = inputRewindStart := by native_decide

private theorem instance_branch : program[instanceEnd]? =
    some (.branch .output eraseStart rejectPc rejectPc) := by native_decide
private theorem frame_branch : program[frameEnd]? =
    some (.branch .output inputRewindStart rejectPc rejectPc) := by native_decide
private theorem reject_lookup : program[rejectPc]? = some .halt := by native_decide
private theorem accept_lookup : program[acceptPc]? = some .halt := by native_decide

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

private theorem continue_blank (pc good : Nat) (c : Configuration)
    (hLookup : program[pc]? = some (.branch .output good rejectPc rejectPc))
    (hBlank : c.outputTape.current = none) :
    RunsFor program (c.resumeAt pc) (c.resumeAt good) 1 := by
  have step : Step program (c.resumeAt pc) (c.resumeAt good) := by
    simp [Step, successors, next, Configuration.resumeAt, hLookup, hBlank,
      Instruction.next, Configuration.tape]
  exact (RunsFor.zero _).succ step

private theorem reject_marked (pc good : Nat) (c : Configuration)
    (hLookup : program[pc]? = some (.branch .output good rejectPc rejectPc))
    (hMarker : c.outputTape.current = some true) :
    RunsFor program (c.resumeAt pc) { c.resumeAt rejectPc with halted := true } 2 := by
  have step : Step program (c.resumeAt pc) (c.resumeAt rejectPc) := by
    simp [Step, successors, next, Configuration.resumeAt, hLookup, hMarker,
      Instruction.next, Configuration.tape]
  have stop : Step program (c.resumeAt rejectPc) { c.resumeAt rejectPc with halted := true } := by
    simp [Step, successors, next, Configuration.resumeAt, reject_lookup, Instruction.next]
  exact ((RunsFor.zero _).succ step).succ stop

private theorem template_stage (raw : List Bool) :
    ∃ (target : Configuration) (used width : Nat) (rest : List Bool) (before : List (Option Bool)),
      used ≤ 9 * raw.length + 21 ∧ width ≤ raw.length + 3 ∧
      RunsFor program (Configuration.initial raw) (target.resumeAt templateEnd) used ∧
      target.inputTape = { Tape.ofBits rest with left := before } ∧
      target.outputTape = { left := List.replicate (3*width) (some false) } ∧
      rest.length ≤ raw.length ∧
      (rest ≠ [] → ∃ n, raw = encodeSecurityParameter n ++ rest ∧ width = n+3 ∧
        before = some false :: List.replicate n (some true)) := by
  obtain ⟨target, used, width, rest, before, hUsed, hWidth, run, hHalt, hInput, hOutput,
    hRest, hPrefix⟩ := SecurityWidthTemplate.runs_any_layout_prefix raw
  obtain ⟨steps, hSteps, embedded⟩ := run.withSubroutine_halted []
    SecurityWidthTemplate.program afterTemplate templateEnd (Nat.zero_le _) rfl hHalt
  refine ⟨target, steps, width, rest, before, by omega, hWidth, ?_, hInput, hOutput, hRest, hPrefix⟩
  rw [template_layout]
  simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded

private theorem rewind_stage (count : Nat) (input output : Tape)
    (hOutput : output.Equivalent { left := List.replicate count (some false) }) :
    ∃ (target : Configuration) (used : Nat), used ≤ 2*count+4 ∧
      RunsFor program { pc := templateEnd, inputTape := input, outputTape := output }
        (target.resumeAt instanceStart) used ∧
      target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent (Tape.ofBits (List.replicate count false)) := by
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hCounter⟩ :=
    FramedProductGuard.rewind_counter_equivalent count input output hOutput
  obtain ⟨steps, hSteps, embedded⟩ := run.withSubroutine_halted
    (SecurityWidthTemplate.program.asSubroutine 0 templateEnd) rewindBitstring.swapTapes
    (FrameWidthCheck.program.asSubroutine instanceStart instanceEnd ++ afterInstance)
    instanceStart (Nat.zero_le _) rfl hHalt
  refine ⟨target, steps, by omega, ?_, hInput, hCounter⟩
  rw [rewind_layout]
  simpa only [Configuration.rebasePc, Program.asSubroutine_length, templateEnd] using embedded

private theorem instance_stage (before : List (Option Bool)) (count : Nat) (bits : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent (Tape.ofBits (List.replicate count false))) :
    ∃ (target : Configuration) (used : Nat), used ≤ 12*count+12 ∧
      RunsFor program { pc := instanceStart, inputTape := input, outputTape := output }
        (target.resumeAt instanceEnd) used ∧
      target.outputTape.current = (if target.pc = 17 then none else some true) ∧
      (target.pc = 17 → ∃ payload rest,
        bits = frame payload ++ rest ∧ payload.length = count ∧
        target.inputTape.Equivalent
          { Tape.ofBits rest with
            left := payload.reverse.map some ++ some false::List.replicate count (some true) ++ before } ∧
        target.outputTape.Equivalent { left := List.replicate count (some false) ++ [none] }) ∧
      (∀ payload rest, bits = frame payload ++ rest → payload.length = count → target.pc = 17) := by
  obtain ⟨canonical, used, hUsed, run, hHalt, hStatus, hAccepted⟩ :=
    FrameWidthCheck.runs_any_loaded before count bits
  have hStart :
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate count false) } : Configuration).Equivalent
      ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ := run.exists_equivalent hStart
  have hActualHalt : actual.halted = true := hEquivalent.2.1.symm.trans hHalt
  obtain ⟨steps, hSteps, embedded⟩ := actualRun.withSubroutine_halted
    preInstance FrameWidthCheck.program afterInstance instanceEnd (Nat.zero_le _) rfl hActualHalt
  refine ⟨actual, steps, by omega, ?_, ?_, ?_, ?_⟩
  · rw [instance_layout]
    simpa only [Configuration.rebasePc, preInstance_length, Nat.add_zero] using embedded
  · simpa only [hEquivalent.1] using hEquivalent.2.2.2.1.symm.trans hStatus
  · intro hAccept
    obtain ⟨payload, rest, hBits, hLength, hPosition, hCounter⟩ :=
      hAccepted (hEquivalent.1.trans hAccept)
    exact ⟨payload, rest, hBits, hLength, hEquivalent.2.2.1.symm.trans hPosition,
      hEquivalent.2.2.2.symm.trans hCounter⟩
  · intro payload rest hBits hLength
    subst bits
    have hCanonicalPc := FrameWidthCheck.accepts_valid_loaded before payload rest count hLength run hHalt
    exact hEquivalent.1.symm.trans hCanonicalPc

private theorem erase_stage (count : Nat) (input output : Tape)
    (hOutput : output.Equivalent { left := List.replicate count (some false) ++ [none] }) :
    ∃ (target : Configuration) (used : Nat), used ≤ 4*count+3 ∧
      RunsFor program { pc := eraseStart, inputTape := input, outputTape := output }
        (target.resumeAt frameStart) used ∧
      target.inputTape.Equivalent input ∧ target.outputTape.Equivalent ({} : Tape) := by
  obtain ⟨target, used, hUsed, run, _, hInput, hBlank⟩ :=
    FramedProductGuard.erase_counter_embedded preErase afterErase frameStart count input output hOutput
  refine ⟨target, used, hUsed, ?_, hInput, hBlank⟩
  rw [erase_layout]
  simpa only [preErase_length] using run

private theorem frame_stage (before : List (Option Bool)) (bits : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent ({} : Tape)) :
    ∃ (target : Configuration) (used : Nat), used ≤ 11*bits.length+8 ∧
      RunsFor program { pc := frameStart, inputTape := input, outputTape := output }
        (target.resumeAt frameEnd) used ∧
      (target.outputTape.current = some true ∨ ∃ payload,
        bits = frame payload ∧ target.inputTape.Equivalent
          { left := (frame payload).reverse.map some ++ before } ∧
        target.outputTape.Equivalent ({} : Tape)) ∧
      (∀ payload, bits = frame payload → target.outputTape.current = none) := by
  obtain ⟨target, used, hUsed, run, hHalt, outcome⟩ :=
    CompleteFrameCheck.runs_any_loaded before bits input output hInput hOutput
  obtain ⟨steps, hSteps, embedded⟩ := run.withSubroutine_halted
    preFrame CompleteFrameCheck.program afterFrame frameEnd (Nat.zero_le _) rfl hHalt
  refine ⟨target, steps, by omega, ?_, outcome, ?_⟩
  · rw [frame_layout]
    simpa only [Configuration.rebasePc, preFrame_length, Nat.add_zero] using embedded
  · intro payload hBits
    subst bits
    exact CompleteFrameCheck.accepted_of_frame_loaded before payload input output hInput hOutput run hHalt

private theorem input_rewind_stage (bits : List Bool) (input output : Tape)
    (hInput : input.Equivalent { left := bits.reverse.map some }) :
    ∃ (target : Configuration) (used : Nat), used ≤ 2*bits.length+4 ∧
      RunsFor program { pc := inputRewindStart, inputTape := input, outputTape := output }
        (target.resumeAt acceptPc) used ∧
      target.inputTape.Equivalent (Tape.ofBits bits) ∧ target.outputTape.Equivalent output := by
  obtain ⟨target, used, hUsed, run, _, hPosition, hOutput⟩ :=
    FramedProductGuard.rewind_input_embedded preInputRewind [.halt, .halt] acceptPc bits input output hInput
  refine ⟨target, used, hUsed, ?_, hPosition, hOutput⟩
  rw [input_rewind_layout]
  simpa only [preInputRewind_length] using run

/-- Every finite raw request either rejects or certifies precisely the
outer input shape needed by the choose-validation body. The accepting path
returns the same physically retained request, with an erased output tape. -/
theorem runs_any (raw : List Bool) :
    ∃ (target : Configuration) (used : Nat),
      used ≤ 100 * (raw.length+1) + 300 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      (target.outputTape.current = some true ∨
        (target.inputTape.Equivalent (Tape.ofBits raw) ∧ target.outputTape.Equivalent ({} : Tape) ∧
          ∃ n instanceBits reply,
            raw = encodeSecurityParameter n ++ frame instanceBits ++ frame reply ∧
            instanceBits.length = 3*(n+3))) := by
  obtain ⟨templ, t₁, width, rest, before, ht₁, hWidth, r₁, hTemplInput, hTemplOutput,
    hRest, hPrefix⟩ := template_stage raw
  obtain ⟨rewound, t₂, ht₂, r₂, hRewindInput, hRewindOutput⟩ :=
    rewind_stage (3*width) templ.inputTape templ.outputTape (by rw [hTemplOutput]; exact Tape.Equivalent.refl _)
  have hJoin₁ : templ.resumeAt templateEnd =
      ({ pc := templateEnd, inputTape := templ.inputTape, outputTape := templ.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₁] at r₂
  have hInput : rewound.inputTape.Equivalent { Tape.ofBits rest with left := before } := by
    rw [← hTemplInput]
    exact hRewindInput
  obtain ⟨checked, t₃, ht₃, r₃, hStatus, hAccepted, _⟩ :=
    instance_stage before (3*width) rest rewound.inputTape rewound.outputTape hInput hRewindOutput
  have hJoin₂ : rewound.resumeAt instanceStart =
      ({ pc := instanceStart, inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₂] at r₃
  have firstRun := (r₁.trans r₂).trans r₃
  by_cases hAccept : checked.pc = 17
  · obtain ⟨instanceBits, tail, hBits, hLength, hPosition, hCounter⟩ := hAccepted hAccept
    have hBlank : checked.outputTape.current = none := by simpa only [hAccept, ↓reduceIte] using hStatus
    have rBranch₁ := continue_blank instanceEnd eraseStart checked instance_branch hBlank
    obtain ⟨erased, t₄, ht₄, r₄, hEraseInput, hEraseOutput⟩ :=
      erase_stage (3*width) checked.inputTape checked.outputTape hCounter
    have hJoin₃ : checked.resumeAt eraseStart =
        ({ pc := eraseStart, inputTape := checked.inputTape, outputTape := checked.outputTape } : Configuration) := by
      simp [Configuration.resumeAt]
    rw [← hJoin₃] at r₄
    let history := instanceBits.reverse.map some ++
      some false::List.replicate (3*width) (some true) ++ before
    have hFrameInput : erased.inputTape.Equivalent { Tape.ofBits tail with left := history } :=
      hEraseInput.trans hPosition
    obtain ⟨framed, t₅, ht₅, r₅, outcome, _⟩ :=
      frame_stage history tail erased.inputTape erased.outputTape hFrameInput hEraseOutput
    have hJoin₄ : erased.resumeAt frameStart =
        ({ pc := frameStart, inputTape := erased.inputTape, outputTape := erased.outputTape } : Configuration) := by
      simp [Configuration.resumeAt]
    rw [← hJoin₄] at r₅
    have secondRun := ((firstRun.trans rBranch₁).trans r₄).trans r₅
    have hTail : tail.length ≤ raw.length := by
      have hLengths := congrArg List.length hBits
      simp only [List.length_append] at hLengths
      omega
    rcases outcome with rejected | ⟨reply, hTailFrame, hSaved, hEmpty⟩
    · have rReject := reject_marked frameEnd inputRewindStart framed frame_branch rejected
      refine ⟨{ framed.resumeAt rejectPc with halted := true },
        t₁+t₂+t₃+1+t₄+t₅+2, by omega, secondRun.trans rReject, rfl, Or.inl ?_⟩
      exact rejected
    · have hRestNonempty : rest ≠ [] := by
        intro hEmptyRest
        have hLengths := congrArg List.length hBits
        simp [hEmptyRest, frame] at hLengths
      obtain ⟨n, hRawPrefix, hWidthEq, hBefore⟩ := hPrefix hRestNonempty
      have hRaw : raw = encodeSecurityParameter n ++ frame instanceBits ++ frame reply := by
        rw [hRawPrefix, hBits, hTailFrame]
        simp only [List.append_assoc]
      have hSavedRaw : framed.inputTape.Equivalent { left := raw.reverse.map some } := by
        rw [hRaw]
        simpa [history, frame, encodeSecurityParameter, List.reverse_append, List.map_append,
          List.map_replicate, List.reverse_replicate, List.append_assoc, hLength, hBefore] using hSaved
      have hFrameBlank : framed.outputTape.current = none := hEmpty.1
      have rBranch₂ := continue_blank frameEnd inputRewindStart framed frame_branch hFrameBlank
      obtain ⟨final, t₆, ht₆, r₆, hFinalInput, hFinalOutput⟩ :=
        input_rewind_stage raw framed.inputTape framed.outputTape hSavedRaw
      have hJoin₅ : framed.resumeAt inputRewindStart =
          ({ pc := inputRewindStart, inputTape := framed.inputTape, outputTape := framed.outputTape } : Configuration) := by
        simp [Configuration.resumeAt]
      rw [← hJoin₅] at r₆
      have hStop : Step program (final.resumeAt acceptPc) { final.resumeAt acceptPc with halted := true } := by
        simp [Step, successors, next, Configuration.resumeAt, accept_lookup, Instruction.next]
      refine ⟨{ final.resumeAt acceptPc with halted := true },
        t₁+t₂+t₃+1+t₄+t₅+1+t₆+1, by omega,
        ((secondRun.trans rBranch₂).trans r₆).succ hStop, rfl, Or.inr ?_⟩
      exact ⟨hFinalInput, hFinalOutput.trans hEmpty, n, instanceBits, reply,
        hRaw, by simpa only [hWidthEq] using hLength⟩
  · have hMarked : checked.outputTape.current = some true := by simpa only [hAccept, ↓reduceIte] using hStatus
    have rReject := reject_marked instanceEnd eraseStart checked instance_branch hMarked
    exact ⟨{ checked.resumeAt rejectPc with halted := true }, t₁+t₂+t₃+2,
      by omega, firstRun.trans rReject, rfl, Or.inl hMarked⟩

/-- Correctly shaped requests always accept, regardless of the response
payload. Only outer framing is checked here; the separate validation body
performs tag, delimiter, range, and subgroup checks on that payload. -/
theorem runs_valid (n : Nat) (instanceBits reply : List Bool)
    (hInstance : instanceBits.length = 3*(n+3)) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    ∃ (target : Configuration) (used : Nat),
      used ≤ 100*(raw.length+1)+300 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits raw) ∧ target.outputTape.Equivalent ({} : Tape) := by
  let rest := frame instanceBits ++ frame reply
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let before := some false::List.replicate n (some true)
  obtain ⟨templ, t₁, ht₁, templateRun, hTemplHalt, hTemplInput, hTemplOutput⟩ :=
    SecurityWidthTemplate.runs_valid n rest
  obtain ⟨u₁, hu₁, embedded⟩ := templateRun.withSubroutine_halted []
    SecurityWidthTemplate.program afterTemplate templateEnd (Nat.zero_le _) rfl hTemplHalt
  have r₁ : RunsFor program (Configuration.initial raw) (templ.resumeAt templateEnd) u₁ := by
    rw [template_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, raw, rest, List.append_assoc] using embedded
  obtain ⟨rewound, t₂, ht₂, r₂, hRewindInput, hRewindOutput⟩ :=
    rewind_stage (3*(n+3)) templ.inputTape templ.outputTape
      (by rw [hTemplOutput]; exact Tape.Equivalent.refl _)
  have hJoin₁ : templ.resumeAt templateEnd =
      ({ pc := templateEnd, inputTape := templ.inputTape, outputTape := templ.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₁] at r₂
  have hInput : rewound.inputTape.Equivalent { Tape.ofBits rest with left := before } := by
    rw [← hTemplInput]
    exact hRewindInput
  obtain ⟨checked, t₃, ht₃, r₃, hStatus, hAccepted, hInstanceValid⟩ :=
    instance_stage before (3*(n+3)) rest rewound.inputTape rewound.outputTape hInput hRewindOutput
  have hJoin₂ : rewound.resumeAt instanceStart =
      ({ pc := instanceStart, inputTape := rewound.inputTape, outputTape := rewound.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₂] at r₃
  have hPc : checked.pc = 17 := hInstanceValid instanceBits (frame reply) rfl hInstance
  obtain ⟨decodedInstance, tail, hBits, hLength, hPosition, hCounter⟩ := hAccepted hPc
  obtain ⟨hDecoded, hTail⟩ := FramedProductGuard.frame_append_unique (3*(n+3))
    instanceBits decodedInstance (frame reply) tail hInstance hLength hBits
  subst decodedInstance
  subst tail
  have hBlank : checked.outputTape.current = none := by simpa only [hPc, ↓reduceIte] using hStatus
  have rBranch₁ := continue_blank instanceEnd eraseStart checked instance_branch hBlank
  obtain ⟨erased, t₄, ht₄, r₄, hEraseInput, hEraseOutput⟩ :=
    erase_stage (3*(n+3)) checked.inputTape checked.outputTape hCounter
  have hJoin₃ : checked.resumeAt eraseStart =
      ({ pc := eraseStart, inputTape := checked.inputTape, outputTape := checked.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₃] at r₄
  let history := instanceBits.reverse.map some ++
    some false::List.replicate (3*(n+3)) (some true) ++ before
  have hFrameInput : erased.inputTape.Equivalent { Tape.ofBits (frame reply) with left := history } :=
    hEraseInput.trans hPosition
  obtain ⟨framed, t₅, ht₅, r₅, outcome, hFrameValid⟩ :=
    frame_stage history (frame reply) erased.inputTape erased.outputTape hFrameInput hEraseOutput
  have hJoin₄ : erased.resumeAt frameStart =
      ({ pc := frameStart, inputTape := erased.inputTape, outputTape := erased.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₄] at r₅
  have hFrameBlank : framed.outputTape.current = none := hFrameValid reply rfl
  rcases outcome with rejected | ⟨decodedReply, hTailFrame, hSaved, hEmpty⟩
  · rw [hFrameBlank] at rejected
    cases rejected
  rw [← hTailFrame] at hSaved
  have hSavedRaw : framed.inputTape.Equivalent { left := raw.reverse.map some } := by
    simpa [raw, history, before, frame, encodeSecurityParameter, List.reverse_append, List.map_append,
      List.map_replicate, List.reverse_replicate, List.append_assoc, hInstance] using hSaved
  have rBranch₂ := continue_blank frameEnd inputRewindStart framed frame_branch hFrameBlank
  obtain ⟨final, t₆, ht₆, r₆, hFinalInput, hFinalOutput⟩ :=
    input_rewind_stage raw framed.inputTape framed.outputTape hSavedRaw
  have hJoin₅ : framed.resumeAt inputRewindStart =
      ({ pc := inputRewindStart, inputTape := framed.inputTape, outputTape := framed.outputTape } : Configuration) := by
    simp [Configuration.resumeAt]
  rw [← hJoin₅] at r₆
  have hStop : Step program (final.resumeAt acceptPc) { final.resumeAt acceptPc with halted := true } := by
    simp [Step, successors, next, Configuration.resumeAt, accept_lookup, Instruction.next]
  have hSizes : n ≤ raw.length ∧ (frame reply).length ≤ raw.length := by
    simp only [raw, frame, encodeSecurityParameter, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  refine ⟨{ final.resumeAt acceptPc with halted := true },
    u₁+t₂+t₃+1+t₄+t₅+1+t₆+1,
    by change u₁+t₂+t₃+1+t₄+t₅+1+t₆+1 ≤ 100*(raw.length+1)+300; omega,
    (((((((r₁.trans r₂).trans r₃).trans rBranch₁).trans r₄).trans r₅).trans rBranch₂).trans r₆).succ hStop,
    rfl, hFinalInput, hFinalOutput.trans hEmpty⟩

def budget (length : Nat) : Nat := 100*(length+1)+300

theorem budget_polynomiallyBounded : PolynomiallyBounded budget :=
  ((PolynomiallyBounded.const 100).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
    (PolynomiallyBounded.const 300)

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt, _⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

end Machine.ChooseOuterGuard
