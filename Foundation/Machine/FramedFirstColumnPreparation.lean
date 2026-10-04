import Foundation.Machine.FramedInstanceColumnPreparation

namespace Machine.FramedFirstColumnPreparation

private def firstReturn : Nat := FramedInstanceColumnPreparation.program.length + 1
private def secondReturn : Nat := firstReturn + OutputColumnRewind.toFirst.length + 1
private def finalReturn : Nat := secondReturn + FramedColumnSlotFill.program.length + 1
private def firstProgram : Program :=
  FramedInstanceColumnPreparation.program.asSubroutine 0 firstReturn
private def secondProgram : Program :=
  OutputColumnRewind.toFirst.asSubroutine firstReturn secondReturn

/-- Parse the instance and first framed element into the shared three-cell
columns. The first element occupies the first slot and the modulus remains
in the third slot. -/
def program : Program :=
  firstProgram ++ secondProgram ++
    FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceColumnPreparation.program
      (secondProgram ++ FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, firstProgram, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine firstProgram OutputColumnRewind.toFirst
      (FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
      secondReturn := by
  simp [program, secondProgram, firstProgram, firstReturn,
    Program.withSubroutine, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (firstProgram ++ secondProgram)
      FramedColumnSlotFill.program [.halt] finalReturn := by
  simp [program, Program.withSubroutine, secondProgram, secondReturn,
    firstProgram, firstReturn, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [third_layout]
    have hOffset : finalReturn = (firstProgram ++ secondProgram).length +
        FramedColumnSlotFill.program.length + 1 + 0 := by
      simp [finalReturn, secondReturn, firstReturn, firstProgram,
        secondProgram, Program.asSubroutine_length, Nat.add_assoc]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

def validBudget (n : Nat) (modulus second third first : List Bool) : Nat :=
  FramedInstanceColumnPreparation.validBudget n modulus second third +
    (2 * (BinaryThirdColumnTemplate.columns modulus).length + 4) +
    (3 * (first.length + 1) + (9 * first.length + 2)) + 4

theorem runs_valid_bounded (n : Nat) (modulus second third first following : List Bool)
    (hModulus : modulus.length = n + 3)
    (hSecond : second.length = modulus.length)
    (hThird : third.length = modulus.length)
    (hFirst : first.length = modulus.length) :
    let instanceBits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ following
    ∃ target used,
      used ≤ validBudget n modulus second third first ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits following with
          left := first.reverse.map some ++
            some false :: List.replicate first.length (some true) ++
              (second ++ third).reverse.map some ++
                modulus.reverse.map some ++
                  some false :: List.replicate instanceBits.length (some true) ++
                    some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some } := by
  dsimp only
  let instanceBits := modulus ++ second ++ third
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame first ++ following
  let columns := BinaryThirdColumnTemplate.columns modulus
  let history : List (Option Bool) :=
    (second ++ third).reverse.map some ++
      modulus.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++
          some false :: List.replicate n (some true)
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    FramedInstanceColumnPreparation.runs_valid_bounded n modulus second third
      (frame first ++ following) hModulus hSecond hThird
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedInstanceColumnPreparation.program
    (secondProgram ++ FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa [raw, instanceBits, List.append_assoc,
      Configuration.rebasePc] using embedded1
  let rewindStart : Configuration :=
    { inputTape := prepared.inputTape,
      outputTape := { left := columns.reverse.map some } }
  let actualRewindStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨u2, hu2, rewindRun, hOutput2⟩ :=
    OutputColumnRewind.toFirst_runs columns prepared.inputTape
  let rewound : Configuration :=
    (rewindBitstringFinish columns prepared.inputTape).swapTapes
  have hRewindStart : rewindStart.Equivalent actualRewindStart := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    simpa [rewindStart, actualRewindStart, columns] using hOutput1.symm
  obtain ⟨actualRewound, actualRewindRun, hRewindEquiv⟩ :=
    (show RunsFor OutputColumnRewind.toFirst rewindStart rewound u2 from rewindRun).exists_equivalent
      hRewindStart
  have hActualHalt2 : actualRewound.halted = true :=
    hRewindEquiv.2.1.symm.trans rfl
  obtain ⟨v2, hv2, embedded2⟩ := actualRewindRun.withSubroutine_halted
    firstProgram OutputColumnRewind.toFirst
    (FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hActualHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      actualRewindStart.rebasePc firstProgram.length := by
    simp [actualRewindStart, Configuration.resumeAt, Configuration.rebasePc,
      firstProgram, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (actualRewound.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let fillStart : Configuration :=
    { inputTape := { Tape.ofBits (frame first ++ following) with left := history },
      outputTape := { Tape.ofBits columns with left := [] } }
  let fillHistory : List (Option Bool) :=
    first.reverse.map some ++
      some false :: List.replicate first.length (some true) ++ history
  let fillFinish : Configuration :=
    { pc := 16,
      inputTape := { Tape.ofBits following with left := fillHistory },
      outputTape :=
        { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some },
      halted := true }
  have hFillEval : evalConfigWithin FramedColumnSlotFill.program fillStart
      (3 * (first.length + 1) + (9 * first.length + 2)) = PMF.pure fillFinish := by
    simpa [fillStart, fillFinish, fillHistory, columns] using
      FramedColumnSlotFill.framed_first_explicit first modulus following
        hFirst history []
  have hFillMem : fillFinish ∈
      (evalConfigWithin FramedColumnSlotFill.program fillStart
        (3 * (first.length + 1) + (9 * first.length + 2))).support := by
    rw [hFillEval]
    simp
  obtain ⟨u3, hu3, fillRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hFillMem).toRunsFor_le
  let actualFillStart : Configuration :=
    { inputTape := actualRewound.inputTape, outputTape := actualRewound.outputTape }
  have hFillStart : fillStart.Equivalent actualFillStart := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have hPreparedInput : prepared.inputTape.Equivalent fillStart.inputTape := by
        simpa [fillStart, history, instanceBits, List.append_assoc] using hInput1
      have hRewoundInput : prepared.inputTape.Equivalent actualRewound.inputTape := by
        exact hRewindEquiv.2.2.1
      exact hPreparedInput.symm.trans hRewoundInput
    · have hRewoundOutput : actualRewound.outputTape.Equivalent (Tape.ofBits columns) :=
        hRewindEquiv.2.2.2.symm.trans hOutput2
      have hEmpty : ({ Tape.ofBits columns with left := [] } : Tape) =
          Tape.ofBits columns := by cases columns <;> rfl
      simpa [fillStart, actualFillStart, hEmpty] using hRewoundOutput.symm
  obtain ⟨actualFillFinish, actualFillRun, hFillEquiv⟩ :=
    fillRun.exists_equivalent hFillStart
  have hActualHalt3 : actualFillFinish.halted = true :=
    hFillEquiv.2.1.symm.trans rfl
  obtain ⟨v3, hv3, embedded3⟩ := actualFillRun.withSubroutine_halted
    (firstProgram ++ secondProgram) FramedColumnSlotFill.program [.halt]
    finalReturn (Nat.zero_le _) rfl hActualHalt3
  have hJoin3 : actualRewound.resumeAt secondReturn =
      actualFillStart.rebasePc (firstProgram ++ secondProgram).length := by
    simp [actualFillStart, Configuration.resumeAt, Configuration.rebasePc,
      firstProgram, secondProgram, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (actualRewound.resumeAt secondReturn)
      (actualFillFinish.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (actualFillFinish.resumeAt finalReturn)
      { actualFillFinish.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ actualFillFinish.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, ?_, ((r1.trans r2).trans r3).succ hStop,
    rfl, ?_, ?_⟩
  · dsimp [validBudget]
    have hColumns : columns.length =
        (BinaryThirdColumnTemplate.columns modulus).length := rfl
    omega
  · simpa [Configuration.resumeAt, fillFinish, fillHistory, history,
      instanceBits, List.append_assoc] using hFillEquiv.2.2.1.symm
  · simpa [Configuration.resumeAt, fillFinish] using hFillEquiv.2.2.2.symm

theorem runs_valid (n : Nat) (modulus second third first following : List Bool)
    (hModulus : modulus.length = n + 3)
    (hSecond : second.length = modulus.length)
    (hThird : third.length = modulus.length)
    (hFirst : first.length = modulus.length) :
    let instanceBits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame instanceBits ++
      frame first ++ following
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits following with
          left := first.reverse.map some ++
            some false :: List.replicate first.length (some true) ++
              (second ++ third).reverse.map some ++
                modulus.reverse.map some ++
                  some false :: List.replicate instanceBits.length (some true) ++
                    some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some } := by
  obtain ⟨target, used, _, run, hHalt, hInput, hOutput⟩ :=
    runs_valid_bounded n modulus second third first following
      hModulus hSecond hThird hFirst
  exact ⟨target, used, run, hHalt, hInput, hOutput⟩

/-- The first-operand column wrapper terminates on every finite request,
including malformed instance and element frames. The unread input remains
a contiguous suffix of the original request. -/
theorem runs_any_suffix (raw : List Bool) :
    ∃ target used remaining before,
      used ≤ 100000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before } ∧
      remaining.length ≤ raw.length := by
  obtain ⟨prepared, u1, remaining1, before1, hu1, run1,
    hHalt1, hInput1, hRest1⟩ :=
    FramedInstanceColumnPreparation.runs_any_suffix raw
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedInstanceColumnPreparation.program
    (secondProgram ++ FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let rewindStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨rewound, u2, hu2, run2, hHalt2, hInput2⟩ :=
    OutputColumnRewind.toFirst_runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    firstProgram OutputColumnRewind.toFirst
    (FramedColumnSlotFill.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      rewindStart.rebasePc firstProgram.length := by
    simp [rewindStart, Configuration.resumeAt, Configuration.rebasePc,
      firstProgram, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (rewound.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let fillStart : Configuration :=
    { inputTape := rewound.inputTape, outputTape := rewound.outputTape }
  obtain ⟨filled, remaining, before, hEval3, hHalt3,
    hInput3, hRest3⟩ :=
    FramedColumnSlotFill.all_context_suffix before1 remaining1
      rewound.outputTape
  have hSuffix : rewound.inputTape =
      { Tape.ofBits remaining1 with left := before1 } := by
    rw [hInput2, hInput1]
  change evalConfigWithin FramedColumnSlotFill.program
    ({ inputTape := { Tape.ofBits remaining1 with left := before1 },
       outputTape := rewound.outputTape } : Configuration)
    (12 * remaining1.length + 3) = PMF.pure filled at hEval3
  have hEval3' : evalConfigWithin FramedColumnSlotFill.program fillStart
      (12 * remaining1.length + 3) = PMF.pure filled := by
    simpa [fillStart, hSuffix] using hEval3
  have hMem : filled ∈ (evalConfigWithin FramedColumnSlotFill.program fillStart
      (12 * remaining1.length + 3)).support := by
    rw [hEval3']
    simp
  obtain ⟨u3, hu3, run3⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem).toRunsFor_le
  obtain ⟨v3, hv3, embedded3⟩ := run3.withSubroutine_halted
    (firstProgram ++ secondProgram) FramedColumnSlotFill.program [.halt]
    finalReturn (Nat.zero_le _) rfl hHalt3
  have hJoin3 : rewound.resumeAt secondReturn =
      fillStart.rebasePc (firstProgram ++ secondProgram).length := by
    simp [fillStart, Configuration.resumeAt, Configuration.rebasePc,
      firstProgram, secondProgram, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (rewound.resumeAt secondReturn)
      (filled.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (filled.resumeAt finalReturn)
      { filled.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hInitialStorage :
      GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial,
      Tape.ofBits, Tape.cells] <;> omega
  have hStorage1 := GuardedCompiler.sourceStorage_le_of_run run1
  have hOutput1 : prepared.outputTape.left.length ≤ prepared.outputTape.cells := by
    simp [Tape.cells]
    omega
  refine ⟨{ filled.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, remaining, before, ?_,
    ((r1.trans r2).trans r3).succ hStop, rfl, ?_, ?_⟩
  · change prepared.inputTape.cells + prepared.outputTape.cells ≤
      (Configuration.initial raw).inputTape.cells +
        (Configuration.initial raw).outputTape.cells + u1 at hStorage1
    change (Configuration.initial raw).inputTape.cells +
      (Configuration.initial raw).outputTape.cells ≤ raw.length + 2 at hInitialStorage
    omega
  · simpa [Configuration.resumeAt] using hInput3
  · omega

theorem runs_any (raw : List Bool) :
    ∃ target used,
      used ≤ 100000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, _, hUsed, run, hHalt, _, _⟩ :=
    runs_any_suffix raw
  exact ⟨target, used, hUsed, run, hHalt⟩

end Machine.FramedFirstColumnPreparation
