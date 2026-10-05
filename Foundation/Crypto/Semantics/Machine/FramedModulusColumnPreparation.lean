import Foundation.Crypto.Semantics.Machine.FramedColumnPreparation

namespace Machine.FramedModulusColumnPreparation

private def firstReturn : Nat := FramedColumnPreparation.program.length + 1
private def finalReturn : Nat := firstReturn + FramedColumnSlotFill.program.length + 1
private def first : Program :=
  FramedColumnPreparation.program.asSubroutine 0 firstReturn

private theorem ofBits_empty_left (bits : List Bool) :
    { Tape.ofBits bits with left := [] } = Tape.ofBits bits := by
  cases bits <;> rfl

/-- The first fixed wrapper stage leaves the actual instance frame unread
and the output head on the third slot. The second stage consumes the frame
header and its first fixed-width field into those physical columns. -/
def program : Program :=
  Program.withSubroutine first FramedColumnSlotFill.program [.halt] finalReturn

private theorem first_layout : program =
    Program.withSubroutine [] FramedColumnPreparation.program
      (FramedColumnSlotFill.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, first, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    change (Program.withSubroutine first FramedColumnSlotFill.program [.halt]
      finalReturn)[finalReturn]? = some .halt
    have hOffset : finalReturn = first.length +
        FramedColumnSlotFill.program.length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

theorem runs_valid (n : Nat) (modulus trailingFields following : List Bool)
    (hWidth : modulus.length = n + 3) :
    let instanceBits := modulus ++ trailingFields
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
    let width := n + 3
    ∃ target used,
      used ≤ 9 * n + 21 + 2 * (3 * width) + 8 +
        (3 * (instanceBits.length + 1) + (9 * modulus.length + 2)) + 1 ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (trailingFields ++ following) with
          left := modulus.reverse.map some ++
            some false :: List.replicate instanceBits.length (some true) ++
              some false :: List.replicate n (some true) } ∧
      target.outputTape.Equivalent
        { left := none :: none ::
            (BinaryThirdColumnTemplate.columns modulus).reverse.map some } := by
  dsimp only
  let instanceBits := modulus ++ trailingFields
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
  let width := n + 3
  obtain ⟨prepared, u1, hu1, run1, hHalt1, hInput1, hOutput1⟩ :=
    FramedColumnPreparation.runs_valid n (frame instanceBits ++ following)
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedColumnPreparation.program
    (FramedColumnSlotFill.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add,
      raw, List.append_assoc] using embedded1
  let before : List (Option Bool) :=
    some false :: List.replicate n (some true)
  let idealStart : Configuration :=
    { inputTape := { Tape.ofBits (frame instanceBits ++ following) with left := before },
      outputTape :=
        (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
          (List.replicate width false)) with left := [] } : Tape).moveRight.moveRight) }
  let idealFinish : Configuration :=
    { pc := 16,
      inputTape :=
        { Tape.ofBits (trailingFields ++ following) with
          left := modulus.reverse.map some ++
            some false :: List.replicate instanceBits.length (some true) ++ before },
      outputTape :=
        { left := none :: none ::
            (BinaryThirdColumnTemplate.columns modulus).reverse.map some },
      halted := true }
  have hEval : evalConfigWithin FramedColumnSlotFill.program idealStart
      (3 * (instanceBits.length + 1) + (9 * modulus.length + 2)) =
      PMF.pure idealFinish := by
    simpa [idealStart, idealFinish, before, width, instanceBits, hWidth,
      List.append_assoc] using
      FramedColumnSlotFill.framed_modulus_explicit modulus trailingFields following before []
  have hMem : idealFinish ∈
      (evalConfigWithin FramedColumnSlotFill.program idealStart
        (3 * (instanceBits.length + 1) + (9 * modulus.length + 2))).support := by
    rw [hEval]
    simp
  obtain ⟨u2, hu2, idealRun⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem).toRunsFor_le
  let actualStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  have hEquivalent : idealStart.Equivalent actualStart := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [show idealStart.inputTape = prepared.inputTape by
        simpa [idealStart, before] using hInput1.symm]
      exact Tape.Equivalent.refl _
    · simpa [idealStart, actualStart, width, ofBits_empty_left] using hOutput1.symm
  obtain ⟨actualFinish, actualRun, hFinalEquiv⟩ :=
    idealRun.exists_equivalent hEquivalent
  have hActualHalt : actualFinish.halted = true := hFinalEquiv.2.1.symm.trans rfl
  obtain ⟨v2, hv2, embedded2⟩ := actualRun.withSubroutine_halted
    first FramedColumnSlotFill.program [.halt] finalReturn
    (Nat.zero_le _) rfl hActualHalt
  have hJoin : prepared.resumeAt firstReturn =
      actualStart.rebasePc first.length := by
    simp [Configuration.resumeAt, Configuration.rebasePc,
      actualStart, first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (actualFinish.resumeAt finalReturn) v2 := by
    rw [hJoin]
    simpa [program] using embedded2
  have hStop : Step program (actualFinish.resumeAt finalReturn)
      { actualFinish.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ actualFinish.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, ?_, (r1.trans r2).succ hStop, rfl, ?_, ?_⟩
  · change v1 + v2 + 1 ≤ 9 * n + 21 + 2 * (3 * width) + 8 +
      (3 * (instanceBits.length + 1) + (9 * modulus.length + 2)) + 1
    have hBits : (List.replicate (3 * width) false).length = 3 * width := by simp
    rw [hBits] at hu1
    omega
  · simpa [Configuration.resumeAt, idealFinish, before, instanceBits,
      List.length_append] using hFinalEquiv.2.2.1.symm
  · simpa [Configuration.resumeAt, idealFinish] using hFinalEquiv.2.2.2.symm

/-- Both native stages terminate on every finite raw input. No validity or
width premise is used; this does not assert successful field extraction. -/
theorem runs_any_suffix (raw : List Bool) :
    ∃ target used remaining before,
      used ≤ 200 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before } ∧
      remaining.length ≤ raw.length := by
  obtain ⟨prepared, u1, width, rest, before, hu1, run1,
    hHalt1, hInput1, _, _, hRest⟩ :=
    FramedColumnPreparation.runs_any_layout raw
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedColumnPreparation.program
    (FramedColumnSlotFill.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (prepared.resumeAt firstReturn) v1 := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
      using embedded1
  let actualStart : Configuration :=
    { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  obtain ⟨finished, remaining, afterInput, hEval, hHalt2,
    hInput2, hRemaining⟩ :=
    FramedColumnSlotFill.all_context_suffix before rest prepared.outputTape
  change evalConfigWithin FramedColumnSlotFill.program
    ({ inputTape := { Tape.ofBits rest with left := before },
       outputTape := prepared.outputTape } : Configuration)
    (12 * rest.length + 3) = PMF.pure finished at hEval
  have hEval' : evalConfigWithin FramedColumnSlotFill.program actualStart
      (12 * rest.length + 3) = PMF.pure finished := by
    simpa [actualStart, hInput1] using hEval
  have hMem : finished ∈
      (evalConfigWithin FramedColumnSlotFill.program actualStart
        (12 * rest.length + 3)).support := by
    rw [hEval']
    simp
  obtain ⟨u2, hu2, run2⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem).toRunsFor_le
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    first FramedColumnSlotFill.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt2
  have hJoin : prepared.resumeAt firstReturn =
      actualStart.rebasePc first.length := by
    simp [Configuration.resumeAt, Configuration.rebasePc,
      actualStart, first, firstReturn, Program.asSubroutine_length]
  have r2 : RunsFor program (prepared.resumeAt firstReturn)
      (finished.resumeAt finalReturn) v2 := by
    rw [hJoin]
    simpa [program] using embedded2
  have hStop : Step program (finished.resumeAt finalReturn)
      { finished.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  refine ⟨{ finished.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, remaining, afterInput, ?_,
    (r1.trans r2).succ hStop, rfl, ?_, ?_⟩
  · omega
  · simpa [Configuration.resumeAt] using hInput2
  · omega

theorem runs_any (raw : List Bool) :
    ∃ target used,
      used ≤ 200 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true := by
  obtain ⟨target, used, _, _, hUsed, run, hHalt, _, _⟩ :=
    runs_any_suffix raw
  exact ⟨target, used, hUsed, run, hHalt⟩

end Machine.FramedModulusColumnPreparation
