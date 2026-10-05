import Foundation.Crypto.Semantics.Machine.FramedInstanceCopy
import Foundation.Crypto.Semantics.Machine.PrimeModulusProjection
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.FramedModulusCopy

private def firstReturn : Nat := FramedInstanceCopy.program.length + 1
private def finalReturn : Nat := firstReturn + PrimeModulusProjection.program.length + 1
private def pre : Program := FramedInstanceCopy.program.asSubroutine 0 firstReturn

/-- One finite instruction list copies a framed instance and projects its
first of three equal-width fields. -/
def program : Program :=
  Program.withSubroutine pre PrimeModulusProjection.program [.halt] finalReturn

/-- A valid framed instance uses at most linear native transition count. -/
def budget (length : Nat) : Nat := 200 * (length + 1)

/-- Bound for arbitrary finite input, including malformed frames. -/
def allInputBudget (length : Nat) : Nat := 300000 * (length + 1)

private theorem first_layout : program =
    Program.withSubroutine [] FramedInstanceCopy.program
      (PrimeModulusProjection.program.asSubroutine firstReturn finalReturn ++ [.halt])
      firstReturn := by
  simp [program, pre, Program.withSubroutine, firstReturn,
    Program.asSubroutine_length]

private theorem second_layout : program =
    Program.withSubroutine pre
      PrimeModulusProjection.program [.halt] finalReturn := by
  rfl

private theorem final_step (c : Configuration)
    (hPc : c.pc = finalReturn) (hActive : c.halted = false) :
    Step program c { c with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    change (Program.withSubroutine pre PrimeModulusProjection.program [.halt]
      finalReturn)[finalReturn]? = some .halt
    have hOffset : finalReturn = pre.length +
        PrimeModulusProjection.program.length + 1 + 0 := by
      simp [finalReturn, firstReturn, pre, Program.asSubroutine_length]
    rw [hOffset, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The two native stages retain the actual tape state at their join. On a
valid three-field instance, the output is the modulus. The following input
cell is written `true`, matching a nonempty next element frame; the exact
right tape is stated below. All-input halting is proved by `runs`. -/
theorem runs_valid (n width : Nat) (modulus second third rest : List Bool)
    (hModulus : modulus.length = width)
    (hSecond : second.length = width)
    (hThird : third.length = width) :
    let bits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame bits ++ rest
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape =
        { left := (false :: List.replicate (3 * width) true ++
            false :: modulus ++ second ++ third).reverse.map some ++
            List.replicate n (some true),
          current := some true, right := (Tape.ofBits rest).right } ∧
      target.outputTape =
        { left := List.replicate (second ++ third).length none ++
            modulus.reverse.map some ++ [none] } ∧
      target.outputBits = modulus ∧
      target.inputTape.current = some true := by
  dsimp only
  let bits := modulus ++ second ++ third
  let raw := encodeSecurityParameter n ++ frame bits ++ rest
  obtain ⟨after, u1, hu1, run1, hHalt1, hInput, hOutputTape, _⟩ :=
    FramedInstanceCopy.runs_valid n bits rest
  obtain ⟨v1, hv1, embedded1⟩ := run1.withSubroutine_halted
    [] FramedInstanceCopy.program
    (PrimeModulusProjection.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial raw)
      (after.resumeAt firstReturn) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add, raw] using embedded1
  have hLeft : after.inputTape.left = bits.reverse.map some ++ some false ::
      List.replicate bits.length (some true) ++
        some false :: List.replicate n (some true) := by
    simpa [List.append_assoc] using congrArg Tape.left hInput
  have hBits : bits = modulus ++ second ++ third := rfl
  have hLeft' : after.inputTape.left =
      (modulus ++ second ++ third).reverse.map some ++ some false ::
        List.replicate (modulus ++ second ++ third).length (some true) ++
          some false :: List.replicate n (some true) := by
    simpa only [hBits] using hLeft
  obtain ⟨finish, u2, hu2, run2, hHalt2, hInput2, hOutput2,
    hOut2, hHead2⟩ :=
    PrimeModulusProjection.runs_valid after.inputTape modulus second third width
      (List.replicate n (some true)) hModulus hSecond hThird hLeft'
  have hStart : after.resumeAt firstReturn =
      (({ inputTape := after.inputTape,
          outputTape := { left := bits.reverse.map some ++ [none] } } :
        Configuration).rebasePc firstReturn) := by
    simp [Configuration.resumeAt, Configuration.rebasePc, hOutputTape]
  rw [hStart] at r1
  obtain ⟨v2, hv2, embedded2⟩ := run2.withSubroutine_halted
    pre
    PrimeModulusProjection.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt2
  have r2 : RunsFor program
      (({ inputTape := after.inputTape,
          outputTape := { left := bits.reverse.map some ++ [none] } } :
        Configuration).rebasePc firstReturn)
      (finish.resumeAt finalReturn) v2 := by
    simpa [second_layout, pre, Program.asSubroutine_length, firstReturn,
      bits, List.reverse_append, List.map_append, List.append_assoc]
      using embedded2
  have hFinal : Step program (finish.resumeAt finalReturn)
      { finish.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hAfterRight : after.inputTape.right = (Tape.ofBits rest).right := by
    simpa using congrArg Tape.right hInput
  refine ⟨{ finish.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, ?_, (r1.trans r2).succ hFinal, rfl,
    ?_, ?_, ?_, ?_⟩
  · have hBits : bits.length ≤ raw.length := by
      simp [bits, raw, frame, encodeSecurityParameter]
      omega
    change v1 + v2 + 1 ≤ 200 * (raw.length + 1)
    change u1 ≤ 26 * raw.length + 15 at hu1
    change u2 ≤ 100 * (bits.length + 1) at hu2
    omega
  · simpa [Configuration.resumeAt, hAfterRight, bits, List.append_assoc]
      using hInput2
  · simpa [Configuration.resumeAt] using hOutput2
  · simpa [Configuration.resumeAt, Configuration.outputBits] using hOut2
  · simpa [Configuration.resumeAt] using hHead2

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- The two native parsing stages stop on every finite bitstring. The
projector receives the actual tapes left by the first stage. -/
theorem runs (bits : List Bool) :
    ∃ finish used, used ≤ allInputBudget bits.length ∧
      RunsFor program (Configuration.initial bits) finish used ∧
      finish.halted = true := by
  obtain ⟨after, u1, hu1, rFirst, hHalt1⟩ := FramedInstanceCopy.runs bits
  obtain ⟨v1, hv1, embed1⟩ := rFirst.withSubroutine_halted
    [] FramedInstanceCopy.program
    (PrimeModulusProjection.program.asSubroutine firstReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt1
  have r1 : RunsFor program (Configuration.initial bits)
      (after.resumeAt firstReturn) v1 := by
    simpa only [← first_layout, Configuration.rebasePc,
      List.length_nil, Nat.zero_add] using embed1
  obtain ⟨projected, u2, hu2, rProject, hHalt2⟩ :=
    PrimeModulusProjection.runs_any after.inputTape after.outputTape
  have hStart : after.resumeAt firstReturn =
      (({ inputTape := after.inputTape,
          outputTape := after.outputTape } : Configuration).rebasePc firstReturn) := by
    simp [Configuration.resumeAt, Configuration.rebasePc]
  rw [hStart] at r1
  obtain ⟨v2, hv2, embed2⟩ := rProject.withSubroutine_halted
    pre PrimeModulusProjection.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt2
  have r2 : RunsFor program
      (({ inputTape := after.inputTape,
          outputTape := after.outputTape } : Configuration).rebasePc firstReturn)
      (projected.resumeAt finalReturn) v2 := by
    simpa [second_layout, pre, Program.asSubroutine_length, firstReturn]
      using embed2
  have hFinal : Step program (projected.resumeAt finalReturn)
      { projected.resumeAt finalReturn with halted := true } :=
    final_step _ rfl rfl
  have hStorage := GuardedCompiler.sourceStorage_le_of_run r1
  have hInitial : (Configuration.initial bits).inputTape.cells +
      (Configuration.initial bits).outputTape.cells ≤ bits.length + 2 := by
    cases bits <;> simp [Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  have hAfter : after.inputTape.cells + after.outputTape.cells ≤
      bits.length + 2 + v1 := by
    simpa [GuardedCompiler.sourceStorage, Configuration.rebasePc]
      using hStorage.trans (Nat.add_le_add_right hInitial v1)
  refine ⟨{ projected.resumeAt finalReturn with halted := true },
    v1 + v2 + 1, ?_, (r1.trans r2).succ hFinal, rfl⟩
  change v1 + v2 + 1 ≤ 300000 * (bits.length + 1)
  change u1 ≤ 26 * bits.length + 15 at hu1
  change u2 ≤ 10000 *
    (after.inputTape.cells + after.outputTape.cells + 1) at hu2
  omega

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (allInputBudget bits.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program := by
  refine ⟨allInputBudget, ?_, haltsWithin⟩
  exact (PolynomiallyBounded.const 300000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

/-- Evaluation of the composed finite code on a valid three-field frame. -/
theorem eval_valid (n width : Nat) (modulus second third rest : List Bool)
    (hModulus : modulus.length = width)
    (hSecond : second.length = width)
    (hThird : third.length = width) :
    let bits := modulus ++ second ++ third
    let raw := encodeSecurityParameter n ++ frame bits ++ rest
    evalWithin program raw (budget raw.length) = PMF.pure (some modulus) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt, _, _, hOutput, _⟩ :=
    runs_valid n width modulus second third rest hModulus hSecond hThird
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

end Machine.FramedModulusCopy
