import Foundation.Crypto.Semantics.Machine.FramedModulusColumnPreparation

namespace Machine.FramedInstanceColumnPreparation

private def firstReturn : Nat := FramedModulusColumnPreparation.program.length + 1
private def secondReturn : Nat := firstReturn + OutputColumnRewind.thirdBoundaryToFirst.length + 1
private def finalReturn : Nat := secondReturn + TwoFieldColumnSkip.program.length + 1
private def first : Program :=
  FramedModulusColumnPreparation.program.asSubroutine 0 firstReturn
private def secondProgram : Program :=
  OutputColumnRewind.thirdBoundaryToFirst.asSubroutine firstReturn secondReturn

/-- Fill the modulus column and then advance past the two remaining
instance fields. The output column block is reused as the skip counter. -/
def program : Program :=
  first ++ secondProgram ++ TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedModulusColumnPreparation.program
      (secondProgram ++ TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first OutputColumnRewind.thirdBoundaryToFirst
      (TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
      secondReturn := by
  simp [program, secondProgram, first, firstReturn,
    Program.withSubroutine, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ secondProgram) TwoFieldColumnSkip.program
      [.halt] finalReturn := by
  simp [program, Program.withSubroutine, secondProgram, secondReturn,
    first, firstReturn, Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [third_layout]
    have hOffset : finalReturn = (first ++ secondProgram).length +
        TwoFieldColumnSkip.program.length + 1 + 0 := by
      simp [finalReturn, secondReturn, firstReturn, secondProgram, first,
        Program.asSubroutine_length, Nat.add_assoc]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Exact additive budget for the three concrete preparation subroutines
on a valid fixed-width instance. -/
def validBudget (n : Nat) (modulus second third : List Bool) : Nat :=
  (9 * n + 21 + 2 * (3 * (n + 3)) + 8 +
    (3 * ((modulus ++ second ++ third).length + 1) +
      (9 * modulus.length + 2)) + 1) +
    (2 * (BinaryThirdColumnTemplate.columns modulus).length + 9) +
    (7 * modulus.length + 2) + 4

/-- A charged trace from a valid encoded instance reaches the first element
frame with the modulus still present in the third column slot. -/
theorem runs_valid_bounded (n : Nat) (modulus second third following : List Bool)
    (hModulus : modulus.length = n + 3)
    (hSecond : second.length = modulus.length)
    (hThird : third.length = modulus.length) :
    let instanceBits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
    ∃ target used,
      used ≤ validBudget n modulus second third ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits following with
          left := (second ++ third).reverse.map some ++
            modulus.reverse.map some ++
              some false :: List.replicate instanceBits.length (some true) ++
                some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        { left := (BinaryThirdColumnTemplate.columns modulus).reverse.map some } := by
  dsimp only
  let instanceBits := modulus ++ second ++ third
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
  let columns := BinaryThirdColumnTemplate.columns modulus
  let beforeInput : List (Option Bool) :=
    modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    FramedModulusColumnPreparation.runs_valid n modulus
      (second ++ third) following (by simpa [instanceBits, List.append_assoc] using hModulus)
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedModulusColumnPreparation.program
    (secondProgram ++ TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa [raw, instanceBits, List.append_assoc,
      Configuration.rebasePc] using embedded1
  let rewindStart : Configuration :=
    { inputTape := prepared.inputTape,
      outputTape := { left := none :: none :: columns.reverse.map some } }
  obtain ⟨rewound, u2, hu2, rewindRun, hHalt2, hInput2, hOutput2⟩ :=
    OutputColumnRewind.thirdBoundaryToFirst_runs columns prepared.inputTape
  let actualRewindStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  have hRewindStart : rewindStart.Equivalent actualRewindStart := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    simpa [rewindStart, actualRewindStart, columns] using hOutput1.symm
  obtain ⟨actualRewound, actualRewindRun, hRewindEquiv⟩ :=
    rewindRun.exists_equivalent hRewindStart
  have hActualHalt2 : actualRewound.halted = true := hRewindEquiv.2.1.symm.trans hHalt2
  obtain ⟨v2, hv2, embedded2⟩ := actualRewindRun.withSubroutine_halted
    first OutputColumnRewind.thirdBoundaryToFirst
    (TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hActualHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      actualRewindStart.rebasePc first.length := by
    simp [actualRewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (actualRewound.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let skipStart : Configuration :=
    { inputTape := { Tape.ofBits (second ++ third ++ following) with left := beforeInput },
      outputTape := { Tape.ofBits columns with left := [] } }
  have hSkipEval : evalConfigWithin TwoFieldColumnSkip.program skipStart
      (7 * modulus.length + 2) =
      PMF.pure
        { pc := 7,
          inputTape := { Tape.ofBits following with
            left := (second ++ third).reverse.map some ++ beforeInput },
          outputTape := { left := columns.reverse.map some },
          halted := true } := by
    simpa [skipStart, columns] using
      TwoFieldColumnSkip.eval_instance_fields modulus second third following
        hSecond hThird beforeInput []
  let skipFinish : Configuration :=
    { pc := 7,
      inputTape := { Tape.ofBits following with
        left := (second ++ third).reverse.map some ++ beforeInput },
      outputTape := { left := columns.reverse.map some },
      halted := true }
  have hSkipMem : skipFinish ∈
      (evalConfigWithin TwoFieldColumnSkip.program skipStart
        (7 * modulus.length + 2)).support := by
    rw [show evalConfigWithin TwoFieldColumnSkip.program skipStart
        (7 * modulus.length + 2) = PMF.pure skipFinish by simpa [skipFinish] using hSkipEval]
    simp
  obtain ⟨u3, hu3, skipRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSkipMem).toRunsFor_le
  let actualSkipStart : Configuration :=
    { inputTape := actualRewound.inputTape, outputTape := actualRewound.outputTape }
  have hSkipStart : skipStart.Equivalent actualSkipStart := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have hInput : prepared.inputTape.Equivalent skipStart.inputTape := by
        simpa [skipStart, beforeInput, instanceBits, List.append_assoc] using hInput1
      have hRewoundInput : prepared.inputTape.Equivalent actualRewound.inputTape := by
        rw [← hInput2]
        exact hRewindEquiv.2.2.1
      exact hInput.symm.trans hRewoundInput
    · have hRewoundOutput : actualRewound.outputTape.Equivalent (Tape.ofBits columns) :=
        hRewindEquiv.2.2.2.symm.trans hOutput2
      have hEmpty : ({ Tape.ofBits columns with left := [] } : Tape) =
          Tape.ofBits columns := by cases columns <;> rfl
      simpa [skipStart, actualSkipStart, hEmpty] using hRewoundOutput.symm
  obtain ⟨actualSkipFinish, actualSkipRun, hSkipEquiv⟩ :=
    skipRun.exists_equivalent hSkipStart
  have hActualHalt3 : actualSkipFinish.halted = true :=
    hSkipEquiv.2.1.symm.trans rfl
  obtain ⟨v3, hv3, embedded3⟩ := actualSkipRun.withSubroutine_halted
    (first ++ secondProgram) TwoFieldColumnSkip.program [.halt]
    finalReturn (Nat.zero_le _) rfl hActualHalt3
  have hJoin3 : actualRewound.resumeAt secondReturn =
      actualSkipStart.rebasePc (first ++ secondProgram).length := by
    simp [actualSkipStart, Configuration.resumeAt, Configuration.rebasePc,
      first, secondProgram, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (actualRewound.resumeAt secondReturn)
      (actualSkipFinish.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (actualSkipFinish.resumeAt finalReturn)
      { actualSkipFinish.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ actualSkipFinish.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, ?_, ((r1.trans r2).trans r3).succ hStop,
    rfl, ?_, ?_⟩
  · dsimp [validBudget]
    simpa only [instanceBits] using
      (show v1 + v2 + v3 + 1 ≤
        (9 * n + 21 + 2 * (3 * (n + 3)) + 8 +
          (3 * ((modulus ++ second ++ third).length + 1) +
            (9 * modulus.length + 2)) + 1) +
        (2 * columns.length + 9) + (7 * modulus.length + 2) + 4 by
        have hAssocLength : (modulus ++ (second ++ third)).length =
            (modulus ++ second ++ third).length := by simp [List.append_assoc]
        omega)
  · have h := hSkipEquiv.2.2.1.symm
    simpa [Configuration.resumeAt, skipFinish, beforeInput, instanceBits,
      List.reverse_append, List.map_append, List.length_append,
      List.append_assoc] using h
  · have h := hSkipEquiv.2.2.2.symm
    simpa [Configuration.resumeAt, skipFinish] using h

theorem runs_valid (n : Nat) (modulus second third following : List Bool)
    (hModulus : modulus.length = n + 3)
    (hSecond : second.length = modulus.length)
    (hThird : third.length = modulus.length) :
    let instanceBits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits following with
          left := (second ++ third).reverse.map some ++
            modulus.reverse.map some ++
              some false :: List.replicate instanceBits.length (some true) ++
                some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        { left := (BinaryThirdColumnTemplate.columns modulus).reverse.map some } := by
  obtain ⟨target, used, _, run, hHalt, hInput, hOutput⟩ :=
    runs_valid_bounded n modulus second third following hModulus hSecond hThird
  exact ⟨target, used, run, hHalt, hInput, hOutput⟩

/-- The instance-column wrapper terminates on every finite request. The
bound includes the arbitrary-tape rewinder and the output-bounded field
skip; malformed fields need not produce a valid column layout. -/
theorem runs_any_suffix (raw : List Bool) :
    ∃ target used remaining before,
      used ≤ 1000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before } ∧
      remaining.length ≤ raw.length := by
  obtain ⟨prepared, u1, afterModulus, beforeModulus, hu1, run1,
    hHalt1, hInput1, hRest1⟩ :=
    FramedModulusColumnPreparation.runs_any_suffix raw
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedModulusColumnPreparation.program
    (secondProgram ++ TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let rewindStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨rewound, u2, hu2, run2, hHalt2, hInput2⟩ :=
    OutputColumnRewind.thirdBoundaryToFirst_runs_any
      prepared.inputTape prepared.outputTape
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    first OutputColumnRewind.thirdBoundaryToFirst
    (TwoFieldColumnSkip.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      rewindStart.rebasePc first.length := by
    simp [rewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (rewound.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let skipStart : Configuration :=
    { inputTape := rewound.inputTape, outputTape := rewound.outputTape }
  obtain ⟨skipped, remaining, before, hEval3, hHalt3,
    hInput3, hRest3⟩ :=
    TwoFieldColumnSkip.all_context_suffix afterModulus beforeModulus
      rewound.outputTape
  have hSuffix : rewound.inputTape =
      { Tape.ofBits afterModulus with left := beforeModulus } := by
    rw [hInput2, hInput1]
  change evalConfigWithin TwoFieldColumnSkip.program
    ({ inputTape := { Tape.ofBits afterModulus with left := beforeModulus },
       outputTape := rewound.outputTape } : Configuration)
    (7 * (rewound.outputTape.right.length + 1) + 2) = PMF.pure skipped at hEval3
  have hEval3' : evalConfigWithin TwoFieldColumnSkip.program skipStart
      (7 * (rewound.outputTape.right.length + 1) + 2) = PMF.pure skipped := by
    simpa [skipStart, hSuffix] using hEval3
  have hMem : skipped ∈ (evalConfigWithin TwoFieldColumnSkip.program skipStart
      (7 * (rewound.outputTape.right.length + 1) + 2)).support := by
    rw [hEval3']
    simp
  obtain ⟨u3, hu3, run3⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem).toRunsFor_le
  obtain ⟨v3, hv3, embedded3⟩ := run3.withSubroutine_halted
    (first ++ secondProgram) TwoFieldColumnSkip.program [.halt]
    finalReturn (Nat.zero_le _) rfl hHalt3
  have hJoin3 : rewound.resumeAt secondReturn =
      skipStart.rebasePc (first ++ secondProgram).length := by
    simp [skipStart, Configuration.resumeAt, Configuration.rebasePc,
      first, secondProgram, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (rewound.resumeAt secondReturn)
      (skipped.resumeAt finalReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  have hStop : Step program (skipped.resumeAt finalReturn)
      { skipped.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hInitialStorage :
      GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial,
      Tape.ofBits, Tape.cells] <;> omega
  have hStorage1 := GuardedCompiler.sourceStorage_le_of_run run1
  have hStorage2 := GuardedCompiler.sourceStorage_le_of_run run2
  have hOutput1 : prepared.outputTape.left.length ≤ prepared.outputTape.cells := by
    simp [Tape.cells]
    omega
  have hOutput2 : rewound.outputTape.right.length ≤ rewound.outputTape.cells := by
    simp [Tape.cells]
  refine ⟨{ skipped.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + 1, remaining, before, ?_,
    ((r1.trans r2).trans r3).succ hStop, rfl, ?_, ?_⟩
  change prepared.inputTape.cells + prepared.outputTape.cells ≤
    (Configuration.initial raw).inputTape.cells +
      (Configuration.initial raw).outputTape.cells + u1 at hStorage1
  change rewound.inputTape.cells + rewound.outputTape.cells ≤
    prepared.inputTape.cells + prepared.outputTape.cells + u2 at hStorage2
  change (Configuration.initial raw).inputTape.cells +
    (Configuration.initial raw).outputTape.cells ≤ raw.length + 2 at hInitialStorage
  omega
  · simpa [Configuration.resumeAt] using hInput3
  · omega

theorem runs_any (raw : List Bool) :
    ∃ target used,
      used ≤ 1000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, _, hUsed, run, hHalt, _, _⟩ :=
    runs_any_suffix raw
  exact ⟨target, used, hUsed, run, hHalt⟩

end Machine.FramedInstanceColumnPreparation
