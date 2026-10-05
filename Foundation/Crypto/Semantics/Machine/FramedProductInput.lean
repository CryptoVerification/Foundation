import Foundation.Crypto.Semantics.Machine.FramedProductColumns
import Foundation.Crypto.Semantics.Machine.ProductColumnTransfer
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedProductInput

private def firstReturn : Nat := FramedProductColumns.program.length + 1
private def secondReturn : Nat := firstReturn + ConsumedInputErasure.program.length + 1
private def thirdReturn : Nat := secondReturn + OutputColumnRewind.secondBoundaryToFirst.length + 1
private def finalReturn : Nat := thirdReturn + ProductColumnTransfer.program.length + 1
private def first : Program := FramedProductColumns.program.asSubroutine 0 firstReturn
private def second : Program := ConsumedInputErasure.program.asSubroutine firstReturn secondReturn
private def third : Program := OutputColumnRewind.secondBoundaryToFirst.asSubroutine secondReturn thirdReturn

/-- Prepare the raw product's standard input tape from a framed request.
Every copy, erase, and rewind is part of the same finite instruction list. -/
def program : Program :=
  first ++ second ++ third ++
    ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedProductColumns.program
      (second ++ third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first ConsumedInputErasure.program
      (third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
      secondReturn := by
  simp [program, second, first, firstReturn,
    Program.withSubroutine, Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) OutputColumnRewind.secondBoundaryToFirst
      (ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
      thirdReturn := by
  simp [program, third, second, secondReturn, first, firstReturn,
    Program.withSubroutine, Program.asSubroutine_length, List.append_assoc,
    Nat.add_assoc]

private theorem fourth_layout : program =
    Program.withSubroutine (first ++ second ++ third) ProductColumnTransfer.program
      [.halt] finalReturn := by
  simp [program, Program.withSubroutine, third, thirdReturn,
    second, secondReturn, first, firstReturn,
    Program.asSubroutine_length, List.append_assoc, Nat.add_assoc]

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [fourth_layout]
    have hOffset : finalReturn = (first ++ second ++ third).length +
        ProductColumnTransfer.program.length + 1 + 0 := by
      simp [finalReturn, thirdReturn, secondReturn, firstReturn,
        first, second, third, Program.asSubroutine_length, Nat.add_assoc]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Explicit stopping budget for a well-formed framed product request. -/
def validBudget (n : Nat) (modulus q g a b : List Bool) : Nat :=
  let raw := encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++
    frame a ++ frame b
  let columns := BinaryColumnSlotFill.fullSlots a b modulus
  FramedProductColumns.validBudget n modulus q g a b +
    (4 * raw.length + 3) + (2 * columns.length + 7) +
    (12 * columns.length + 12) + 5

theorem runs_valid_bounded (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length) :
    let instanceBits := modulus ++ q ++ g
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame a ++ frame b
    let columns := BinaryColumnSlotFill.fullSlots a b modulus
    ∃ target used,
      used ≤ validBudget n modulus q g a b ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits columns) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let instanceBits := modulus ++ q ++ g
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame a ++ frame b
  let columns := BinaryColumnSlotFill.fullSlots a b modulus
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    FramedProductColumns.runs_valid_bounded n modulus q g a b [] hModulus hQ hG hA hB
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedProductColumns.program
    (second ++ third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa [raw, instanceBits, List.append_assoc,
      Configuration.rebasePc] using embedded1
  let eraseStart : Configuration :=
    { inputTape := { left := raw.reverse.map some ++ [none] },
      outputTape := prepared.outputTape }
  let actualEraseStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨erased, u2, hu2, eraseRun, hHalt2, hBlank2, hOutput2⟩ :=
    ConsumedInputErasure.runs raw prepared.outputTape
  have hEraseStart : eraseStart.Equivalent actualEraseStart := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    have hHistory : prepared.inputTape.Equivalent
        ({ left := raw.reverse.map some } : Tape) := by
      have hPrefix := FramedProductColumns.consumed_prefix_reverse
        n modulus q g a b
      have hPrefix' : raw.reverse.map some =
          b.reverse.map some ++
            some false :: List.replicate b.length (some true) ++
              a.reverse.map some ++
                some false :: List.replicate a.length (some true) ++
                  (q ++ g).reverse.map some ++
                    modulus.reverse.map some ++
                      some false :: List.replicate instanceBits.length (some true) ++
                        some false :: List.replicate n (some true) := by
        simpa [raw, instanceBits, List.append_assoc] using hPrefix
      rw [hPrefix']
      simpa [Tape.ofBits, instanceBits, List.append_assoc] using hInput1
    exact (ConsumedInputErasure.outer_blank raw).symm.trans hHistory.symm
  obtain ⟨actualErased, actualEraseRun, hEraseEquiv⟩ :=
    (show RunsFor ConsumedInputErasure.program eraseStart erased u2 from eraseRun).exists_equivalent
      hEraseStart
  have hActualHalt2 : actualErased.halted = true := hEraseEquiv.2.1.symm.trans hHalt2
  obtain ⟨v2, hv2, embedded2⟩ := actualEraseRun.withSubroutine_halted
    first ConsumedInputErasure.program
    (third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hActualHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      actualEraseStart.rebasePc first.length := by
    simp [actualEraseStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (actualErased.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let rewindStart : Configuration :=
    { inputTape := actualErased.inputTape,
      outputTape := { left := none :: columns.reverse.map some } }
  let actualRewindStart : Configuration :=
    { inputTape := actualErased.inputTape, outputTape := actualErased.outputTape }
  obtain ⟨rewound, u3, hu3, rewindRun, hHalt3, hInput3, hOutput3⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs columns actualErased.inputTape
  have hRewindStart : rewindStart.Equivalent actualRewindStart := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    have hActualOutput : actualErased.outputTape.Equivalent
        ({ left := none :: columns.reverse.map some } : Tape) :=
      (hEraseEquiv.2.2.2.symm.trans
        (by rw [hOutput2]; exact Tape.Equivalent.refl _)).trans
          (by simpa [columns] using hOutput1)
    exact hActualOutput.symm
  obtain ⟨actualRewound, actualRewindRun, hRewindEquiv⟩ :=
    rewindRun.exists_equivalent hRewindStart
  have hActualHalt3 : actualRewound.halted = true :=
    hRewindEquiv.2.1.symm.trans hHalt3
  obtain ⟨v3, hv3, embedded3⟩ := actualRewindRun.withSubroutine_halted
    (first ++ second) OutputColumnRewind.secondBoundaryToFirst
    (ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    thirdReturn (Nat.zero_le _) rfl hActualHalt3
  have hJoin3 : actualErased.resumeAt secondReturn =
      actualRewindStart.rebasePc (first ++ second).length := by
    simp [actualRewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (actualErased.resumeAt secondReturn)
      (actualRewound.resumeAt thirdReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  let transferStart : Configuration := (Configuration.initial columns).swapTapes
  let actualTransferStart : Configuration :=
    { inputTape := actualRewound.inputTape, outputTape := actualRewound.outputTape }
  obtain ⟨transferred, u4, hu4, transferRun, hHalt4, hInput4, hOutput4⟩ :=
    ProductColumnTransfer.runs columns
  have hTransferStart : transferStart.Equivalent actualTransferStart := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have hActualBlank : actualErased.inputTape.Equivalent ({} : Tape) :=
        hEraseEquiv.2.2.1.symm.trans hBlank2
      have hPreserved : actualRewound.inputTape.Equivalent actualErased.inputTape := by
        have h := hRewindEquiv.2.2.1.symm
        rw [hInput3] at h
        exact h
      simpa [transferStart, Configuration.swapTapes, Configuration.initial] using
        (hPreserved.trans hActualBlank).symm
    · simpa [transferStart, Configuration.swapTapes, Configuration.initial] using
        hOutput3.symm.trans hRewindEquiv.2.2.2
  obtain ⟨actualTransferred, actualTransferRun, hTransferEquiv⟩ :=
    (show RunsFor ProductColumnTransfer.program transferStart transferred u4 from transferRun).exists_equivalent
      hTransferStart
  have hActualHalt4 : actualTransferred.halted = true :=
    hTransferEquiv.2.1.symm.trans hHalt4
  obtain ⟨v4, hv4, embedded4⟩ := actualTransferRun.withSubroutine_halted
    (first ++ second ++ third) ProductColumnTransfer.program [.halt]
    finalReturn (Nat.zero_le _) rfl hActualHalt4
  have hJoin4 : actualRewound.resumeAt thirdReturn =
      actualTransferStart.rebasePc (first ++ second ++ third).length := by
    simp [actualTransferStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, third, thirdReturn, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r4 : RunsFor program (actualRewound.resumeAt thirdReturn)
      (actualTransferred.resumeAt finalReturn) v4 := by
    rw [hJoin4, fourth_layout]
    exact embedded4
  have hStop : Step program (actualTransferred.resumeAt finalReturn)
      { actualTransferred.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ actualTransferred.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + v4 + 1,
    ?_, (((r1.trans r2).trans r3).trans r4).succ hStop, rfl, ?_, ?_⟩
  · dsimp [validBudget]
    have hRaw : raw.length =
        (encodeSecurityParameter n ++ frame (modulus ++ q ++ g) ++
          frame a ++ frame b).length := rfl
    have hColumns : columns.length =
        (BinaryColumnSlotFill.fullSlots a b modulus).length := rfl
    omega
  · simpa [Configuration.resumeAt] using hTransferEquiv.2.2.1.symm.trans hInput4
  · simpa [Configuration.resumeAt] using hTransferEquiv.2.2.2.symm.trans hOutput4

theorem runs_valid (n : Nat) (modulus q g a b : List Bool)
    (hModulus : modulus.length = n + 3)
    (hQ : q.length = modulus.length)
    (hG : g.length = modulus.length)
    (hA : a.length = modulus.length)
    (hB : b.length = modulus.length) :
    let instanceBits := modulus ++ q ++ g
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame a ++ frame b
    let columns := BinaryColumnSlotFill.fullSlots a b modulus
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits columns) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  obtain ⟨target, used, _, run, hHalt, hInput, hOutput⟩ :=
    runs_valid_bounded n modulus q g a b hModulus hQ hG hA hB
  exact ⟨target, used, run, hHalt, hInput, hOutput⟩

/-- The complete framed-input preparation terminates on every finite raw
request. This does not assert that malformed inputs produce arithmetic
columns with valid values. -/
theorem runs_any_with_boundary (raw : List Bool) :
    ∃ target used before,
      used ≤ 10000000000000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.left = none :: before := by
  obtain ⟨prepared, u1, hu1, run1, hHalt1⟩ :=
    FramedProductColumns.runs_any raw
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedProductColumns.program
    (second ++ third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let eraseStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨erased, u2, hu2, run2, hHalt2, _⟩ :=
    ConsumedInputErasure.runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    first ConsumedInputErasure.program
    (third ++ ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hHalt2
  have hJoin2 : prepared.resumeAt firstReturn =
      eraseStart.rebasePc first.length := by
    simp [eraseStart, Configuration.resumeAt, Configuration.rebasePc,
      first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (erased.resumeAt secondReturn) v2 := by
    rw [hJoin2, second_layout]
    exact embedded2
  let rewindStart : Configuration :=
    { inputTape := erased.inputTape, outputTape := erased.outputTape }
  obtain ⟨rewound, u3, hu3, run3, hHalt3, _⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs_any erased.inputTape erased.outputTape
  obtain ⟨v3, hv3, embedded3⟩ := run3.withSubroutine_halted
    (first ++ second) OutputColumnRewind.secondBoundaryToFirst
    (ProductColumnTransfer.program.asSubroutine thirdReturn finalReturn ++ [.halt])
    thirdReturn (Nat.zero_le _) rfl hHalt3
  have hJoin3 : erased.resumeAt secondReturn =
      rewindStart.rebasePc (first ++ second).length := by
    simp [rewindStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r3 : RunsFor program (erased.resumeAt secondReturn)
      (rewound.resumeAt thirdReturn) v3 := by
    rw [hJoin3, third_layout]
    exact embedded3
  let transferStart : Configuration :=
    { inputTape := rewound.inputTape, outputTape := rewound.outputTape }
  obtain ⟨transferred, u4, before, hu4, run4, hHalt4, hBoundary4⟩ :=
    ProductColumnTransfer.runs_any_with_boundary rewound.inputTape rewound.outputTape
  obtain ⟨v4, hv4, embedded4⟩ := run4.withSubroutine_halted
    (first ++ second ++ third) ProductColumnTransfer.program [.halt]
    finalReturn (Nat.zero_le _) rfl hHalt4
  have hJoin4 : rewound.resumeAt thirdReturn =
      transferStart.rebasePc (first ++ second ++ third).length := by
    simp [transferStart, Configuration.resumeAt, Configuration.rebasePc,
      first, second, third, thirdReturn, secondReturn, firstReturn,
      Program.asSubroutine_length, Nat.add_assoc]
  have r4 : RunsFor program (rewound.resumeAt thirdReturn)
      (transferred.resumeAt finalReturn) v4 := by
    rw [hJoin4, fourth_layout]
    exact embedded4
  have hStop : Step program (transferred.resumeAt finalReturn)
      { transferred.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hInitialStorage :
      GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial,
      Tape.ofBits, Tape.cells] <;> omega
  have hStorage1 := GuardedCompiler.sourceStorage_le_of_run run1
  have hStorage2 := GuardedCompiler.sourceStorage_le_of_run run2
  have hStorage3 := GuardedCompiler.sourceStorage_le_of_run run3
  have hInput2 : prepared.inputTape.left.length ≤ prepared.inputTape.cells := by
    simp [Tape.cells]; omega
  have hOutput3 : erased.outputTape.left.length ≤ erased.outputTape.cells := by
    simp [Tape.cells]; omega
  refine ⟨{ transferred.resumeAt finalReturn with halted := true },
    v1 + v2 + v3 + v4 + 1, before, ?_,
    (((r1.trans r2).trans r3).trans r4).succ hStop, rfl, ?_⟩
  change prepared.inputTape.cells + prepared.outputTape.cells ≤
    (Configuration.initial raw).inputTape.cells +
      (Configuration.initial raw).outputTape.cells + u1 at hStorage1
  change erased.inputTape.cells + erased.outputTape.cells ≤
    prepared.inputTape.cells + prepared.outputTape.cells + u2 at hStorage2
  change rewound.inputTape.cells + rewound.outputTape.cells ≤
    erased.inputTape.cells + erased.outputTape.cells + u3 at hStorage3
  change (Configuration.initial raw).inputTape.cells +
    (Configuration.initial raw).outputTape.cells ≤ raw.length + 2 at hInitialStorage
  · omega
  · simpa [Configuration.resumeAt] using hBoundary4

theorem runs_any (raw : List Bool) :
    ∃ target used,
      used ≤ 10000000000000000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, hUsed, run, hHalt, _⟩ := runs_any_with_boundary raw
  exact ⟨target, used, hUsed, run, hHalt⟩

def anyBudget (length : Nat) : Nat :=
  10000000000000000 * (length + 1)

theorem anyBudget_polynomiallyBounded : PolynomiallyBounded anyBudget := by
  change PolynomiallyBounded (fun n => 10000000000000000 * (n + 1))
  exact (PolynomiallyBounded.const 10000000000000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (anyBudget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨anyBudget, anyBudget_polynomiallyBounded, haltsWithin⟩

end Machine.FramedProductInput
