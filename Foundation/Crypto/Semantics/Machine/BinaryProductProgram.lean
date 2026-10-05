import Foundation.Crypto.Semantics.Machine.BinaryProductFinalization

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinaryProductProgram

open BinaryProductSelection

private def initialization : Program := BinaryProductInitialization.program.asSubroutine 0 123
private def loopExit : Nat := 120 + BinaryProductLoop.program.length + 1
private def finishExit : Nat := loopExit + BinaryProductFinalization.program.length + 1
private def beforeFinish : Program := initialization ++
  BinaryProductLoop.program.swapTapes.asSubroutine 120 loopExit

/-- One fixed finite native program: initialize a physical product matrix,
consume its multiplier bits in the native loop, erase the matrix, and copy
the accumulator onto the actual output tape. Static tape relabeling is a
change of instruction operands, not a run-time swap or a fresh tape load. -/
def program : Program := Program.withSubroutine beforeFinish
  BinaryProductFinalization.program.swapTapes [.halt] finishExit

def budget (length : Nat) : Nat := 1000000 * (length + 1) ^ 4

private theorem initialization_length : initialization.length = 120 := by
  simp [initialization, show BinaryProductInitialization.program.length = 119 from rfl]

private theorem beforeFinish_length : beforeFinish.length = loopExit := by
  native_decide

private theorem initialization_layout : program = Program.withSubroutine []
    BinaryProductInitialization.program
    (BinaryProductLoop.program.swapTapes.asSubroutine 120 loopExit ++
      BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) 123 := by
  native_decide

private theorem loop_layout : program = Program.withSubroutine initialization
    BinaryProductLoop.program.swapTapes
    (BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) loopExit := by
  native_decide

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp only [program, Program.withSubroutine, beforeFinish, initialization, List.mem_append, not_or]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
  · exact Program.asSubroutine_no_randomBit _ BinaryProductInitialization.no_randomBit _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ BinaryProductLoop.no_randomBit) _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ BinaryProductFinalization.no_randomBit) _ _ tape

/-- Every finite raw input terminates under the same fourth-degree bound.
Incomplete trailing triples and numerically invalid moduli need no numeric
validity assumptions. This theorem concerns stopping and fixed output width;
the modular arithmetic specification is established separately. -/
theorem runs_from_components (input : List Bool)
    (rawColumns : List BinaryModularAddition.Column) (initialized : Configuration)
    (hWidth : rawColumns.length ≤ input.length) (hInitHalt : initialized.halted = true)
    (hInitInput : initialized.inputTape = { left := input.reverse.map some })
    (hInitOutput : initialized.outputTape = { left := (BinaryProductInitialization.matrix rawColumns).reverse.map some })
    (hInitEval : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * (input.length + 1)) = PMF.pure initialized)
    (finalColumns : List Column) (finalSaved : List (Option Bool))
    (loopTarget : Configuration) (loopSteps : Nat)
    (hFinalWidth : finalColumns.length = (initialColumns rawColumns).length)
    (hLoopBound : loopSteps ≤ BinaryProductLoop.budget (initialColumns rawColumns).length
      (pendingCount (initialColumns rawColumns)))
    (loopRun : RunsFor BinaryProductLoop.program
      (BinaryProductLoop.start (initialColumns rawColumns) (input.reverse.map some)) loopTarget loopSteps)
    (hLoopHalt : loopTarget.halted = true)
    (hLoopInput : loopTarget.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] })
    (hLoopOutput : loopTarget.outputTape.Equivalent { left := finalSaved }) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget input.length ∧
      RunsFor program (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = finalColumns.map Column.accumulator ∧
      target.outputTape.Equivalent
        { left := (finalColumns.map Column.accumulator).reverse.map some ++ [none],
          right := List.replicate ((matrix finalColumns).length - finalColumns.length) none } := by
  obtain ⟨s1, u1, hu1, r1, e1⟩ := nativeCall_of_eval [] BinaryProductInitialization.program
    (BinaryProductLoop.program.swapTapes.asSubroutine 120 loopExit ++
      BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) 123
    (Configuration.initial input) initialized (Configuration.initial input) (17 * (input.length + 1))
    (by change 0 ≤ _; omega) rfl hInitHalt hInitEval (Configuration.Equivalent.refl _)
  rw [← initialization_layout] at r1
  let columns := initialColumns rawColumns
  let saved := input.reverse.map some
  have loopLayout : (((BinaryProductLoop.start columns saved).swapTapes).rebasePc
      initialization.length).Equivalent s1 := by
    refine ⟨?_, e1.2.1, ?_, ?_⟩
    · change initialization.length + 3 = s1.pc
      rw [initialization_length]
      exact e1.1
    · have same := e1.2.2.1
      change initialized.inputTape.Equivalent s1.inputTape at same
      rw [hInitInput] at same
      exact same
    · have same := e1.2.2.2
      change initialized.outputTape.Equivalent s1.outputTape at same
      rw [hInitOutput] at same
      simpa only [columns, BinaryProductLoop.start, selectionFromEnd, initialColumns_matrix,
        Configuration.rebasePc, Configuration.swapTapes] using same
  obtain ⟨u2, hu2, embeddedLoop⟩ := loopRun.swapTapes.withSubroutine_halted initialization
    BinaryProductLoop.program.swapTapes
    (BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) loopExit
    (by rw [Program.swapTapes_length]; exact BinaryProductLoop.entry_in_range) rfl hLoopHalt
  obtain ⟨s2, r2, e2⟩ := embeddedLoop.exists_equivalent loopLayout
  rw [← loop_layout] at r2
  obtain ⟨finished, finishSteps, hFinishBound, finishRun, hFinishHalt, hResult,
    hFinishLayout⟩ :=
    BinaryProductFinalization.runs_with_layout finalColumns finalSaved
  have finishLayout : (((BinaryProductFinalization.start finalColumns finalSaved).swapTapes).rebasePc
      beforeFinish.length).Equivalent s2 := by
    refine ⟨?_, e2.2.1, ?_, ?_⟩
    · change beforeFinish.length + 0 = s2.pc
      rw [beforeFinish_length, Nat.add_zero]
      exact e2.1
    · exact hLoopOutput.symm.trans e2.2.2.1
    · exact hLoopInput.symm.trans e2.2.2.2
  obtain ⟨u3, hu3, embeddedFinish⟩ := finishRun.swapTapes.withSubroutine_halted beforeFinish
    BinaryProductFinalization.program.swapTapes [.halt] finishExit
    (by change 0 ≤ _; omega) rfl hFinishHalt
  obtain ⟨s3, r3, e3⟩ := embeddedFinish.exists_equivalent finishLayout
  have last : Step program s3 { s3 with halted := true } := by
    have hp : s3.pc = finishExit := e3.1.symm
    have ha : s3.halted = false := e3.2.1.symm
    have lookup : program[finishExit]? = some .halt := by native_decide
    simp [Step, successors, next, hp, ha, lookup, Instruction.next]
  have hColumns : columns.length = rawColumns.length := by simp [columns, initialColumns]
  have hSourceSize : columns.length ≤ input.length := hColumns ▸ hWidth
  have hFinalWidth' : finalColumns.length = columns.length := hFinalWidth
  have hSize : finalColumns.length ≤ input.length := hFinalWidth' ▸ hSourceSize
  have hCount : pendingCount columns ≤ columns.length := List.length_filter_le _ _
  have hWidthBudget : BinaryProductLoop.budget columns.length (pendingCount columns) ≤
      BinaryProductLoop.widthBudget columns.length := Nat.mul_le_mul_right _ (Nat.add_le_add_right hCount 1)
  have hNativeBound : u1 + u2 + u3 + 1 ≤ budget input.length := by
    have hPoly := BinaryProductLoop.widthBudget_le columns.length
    have hPow : (columns.length + 1) ^ 4 ≤ (input.length + 1) ^ 4 :=
      Nat.pow_le_pow_left (by omega) _
    have hLinear : input.length + 1 ≤ (input.length + 1) ^ 4 := le_self_pow (by omega) (by decide)
    have hLoop : u2 ≤ 297220 * (input.length + 1) ^ 4 :=
      hu2.trans (hLoopBound.trans (hWidthBudget.trans (hPoly.trans (Nat.mul_le_mul_left _ hPow))))
    have hFinish : u3 ≤ 58 * input.length + 15 := by
      have h := hu3.trans hFinishBound
      dsimp only [BinaryProductFinalization.budget] at h
      omega
    dsimp only [budget]
    omega
  refine ⟨{ s3 with halted := true }, u1 + u2 + u3 + 1,
    hNativeBound, ((r1.trans r2).trans r3).succ last, rfl, ?_, ?_⟩
  have same := e3.2.2.2.bits.symm
  change s3.outputTape.bits = finished.inputTape.bits at same
  exact same.trans hResult
  have hSameTape := e3.2.2.2.symm
  change s3.outputTape.Equivalent finished.inputTape at hSameTape
  exact hSameTape.trans hFinishLayout


/-- The product core also runs with caller cells retained behind the raw
input. Its arithmetic loop carries that exact prefix through the matrix,
without reloading a canonical input tape. -/
theorem runs_from_components_saved (input : List Bool)
    (before : List (Option Bool))
    (rawColumns : List BinaryModularAddition.Column) (initialized : Configuration)
    (hWidth : rawColumns.length ≤ input.length) (hInitHalt : initialized.halted = true)
    (hInitInput : initialized.inputTape = { left := input.reverse.map some ++ before })
    (hInitOutput : initialized.outputTape = { left := (BinaryProductInitialization.matrix rawColumns).reverse.map some })
    (hInitEval : evalConfigWithin BinaryProductInitialization.program ({ inputTape := { Tape.ofBits input with left := before } } : Configuration)
      (17 * (input.length + 1)) = PMF.pure initialized)
    (finalColumns : List Column) (finalSaved : List (Option Bool))
    (loopTarget : Configuration) (loopSteps : Nat)
    (hFinalWidth : finalColumns.length = (initialColumns rawColumns).length)
    (hLoopBound : loopSteps ≤ BinaryProductLoop.budget (initialColumns rawColumns).length
      (pendingCount (initialColumns rawColumns)))
    (loopRun : RunsFor BinaryProductLoop.program
      (BinaryProductLoop.start (initialColumns rawColumns) (input.reverse.map some ++ before)) loopTarget loopSteps)
    (hLoopHalt : loopTarget.halted = true)
    (hLoopInput : loopTarget.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] })
    (hLoopOutput : loopTarget.outputTape.Equivalent { left := finalSaved }) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget input.length ∧
      RunsFor program ({ inputTape := { Tape.ofBits input with left := before } } : Configuration) target used ∧
      target.halted = true ∧ target.outputBits = finalColumns.map Column.accumulator ∧
      target.outputTape.Equivalent
        { left := (finalColumns.map Column.accumulator).reverse.map some ++ [none],
          right := List.replicate ((matrix finalColumns).length - finalColumns.length) none } := by
  obtain ⟨s1, u1, hu1, r1, e1⟩ := nativeCall_of_eval [] BinaryProductInitialization.program
    (BinaryProductLoop.program.swapTapes.asSubroutine 120 loopExit ++
      BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) 123
    ({ inputTape := { Tape.ofBits input with left := before } } : Configuration) initialized ({ inputTape := { Tape.ofBits input with left := before } } : Configuration) (17 * (input.length + 1))
    (by change 0 ≤ _; omega) rfl hInitHalt hInitEval (Configuration.Equivalent.refl _)
  rw [← initialization_layout] at r1
  let columns := initialColumns rawColumns
  let saved := input.reverse.map some ++ before
  have loopLayout : (((BinaryProductLoop.start columns saved).swapTapes).rebasePc
      initialization.length).Equivalent s1 := by
    refine ⟨?_, e1.2.1, ?_, ?_⟩
    · change initialization.length + 3 = s1.pc
      rw [initialization_length]
      exact e1.1
    · have same := e1.2.2.1
      change initialized.inputTape.Equivalent s1.inputTape at same
      rw [hInitInput] at same
      exact same
    · have same := e1.2.2.2
      change initialized.outputTape.Equivalent s1.outputTape at same
      rw [hInitOutput] at same
      simpa only [columns, BinaryProductLoop.start, selectionFromEnd, initialColumns_matrix,
        Configuration.rebasePc, Configuration.swapTapes] using same
  obtain ⟨u2, hu2, embeddedLoop⟩ := loopRun.swapTapes.withSubroutine_halted initialization
    BinaryProductLoop.program.swapTapes
    (BinaryProductFinalization.program.swapTapes.asSubroutine loopExit finishExit ++ [.halt]) loopExit
    (by rw [Program.swapTapes_length]; exact BinaryProductLoop.entry_in_range) rfl hLoopHalt
  obtain ⟨s2, r2, e2⟩ := embeddedLoop.exists_equivalent loopLayout
  rw [← loop_layout] at r2
  obtain ⟨finished, finishSteps, hFinishBound, finishRun, hFinishHalt, hResult,
    hFinishLayout⟩ :=
    BinaryProductFinalization.runs_with_layout finalColumns finalSaved
  have finishLayout : (((BinaryProductFinalization.start finalColumns finalSaved).swapTapes).rebasePc
      beforeFinish.length).Equivalent s2 := by
    refine ⟨?_, e2.2.1, ?_, ?_⟩
    · change beforeFinish.length + 0 = s2.pc
      rw [beforeFinish_length, Nat.add_zero]
      exact e2.1
    · exact hLoopOutput.symm.trans e2.2.2.1
    · exact hLoopInput.symm.trans e2.2.2.2
  obtain ⟨u3, hu3, embeddedFinish⟩ := finishRun.swapTapes.withSubroutine_halted beforeFinish
    BinaryProductFinalization.program.swapTapes [.halt] finishExit
    (by change 0 ≤ _; omega) rfl hFinishHalt
  obtain ⟨s3, r3, e3⟩ := embeddedFinish.exists_equivalent finishLayout
  have last : Step program s3 { s3 with halted := true } := by
    have hp : s3.pc = finishExit := e3.1.symm
    have ha : s3.halted = false := e3.2.1.symm
    have lookup : program[finishExit]? = some .halt := by native_decide
    simp [Step, successors, next, hp, ha, lookup, Instruction.next]
  have hColumns : columns.length = rawColumns.length := by simp [columns, initialColumns]
  have hSourceSize : columns.length ≤ input.length := hColumns ▸ hWidth
  have hFinalWidth' : finalColumns.length = columns.length := hFinalWidth
  have hSize : finalColumns.length ≤ input.length := hFinalWidth' ▸ hSourceSize
  have hCount : pendingCount columns ≤ columns.length := List.length_filter_le _ _
  have hWidthBudget : BinaryProductLoop.budget columns.length (pendingCount columns) ≤
      BinaryProductLoop.widthBudget columns.length := Nat.mul_le_mul_right _ (Nat.add_le_add_right hCount 1)
  have hNativeBound : u1 + u2 + u3 + 1 ≤ budget input.length := by
    have hPoly := BinaryProductLoop.widthBudget_le columns.length
    have hPow : (columns.length + 1) ^ 4 ≤ (input.length + 1) ^ 4 :=
      Nat.pow_le_pow_left (by omega) _
    have hLinear : input.length + 1 ≤ (input.length + 1) ^ 4 := le_self_pow (by omega) (by decide)
    have hLoop : u2 ≤ 297220 * (input.length + 1) ^ 4 :=
      hu2.trans (hLoopBound.trans (hWidthBudget.trans (hPoly.trans (Nat.mul_le_mul_left _ hPow))))
    have hFinish : u3 ≤ 58 * input.length + 15 := by
      have h := hu3.trans hFinishBound
      dsimp only [BinaryProductFinalization.budget] at h
      omega
    dsimp only [budget]
    omega
  refine ⟨{ s3 with halted := true }, u1 + u2 + u3 + 1,
    hNativeBound, ((r1.trans r2).trans r3).succ last, rfl, ?_, ?_⟩
  have same := e3.2.2.2.bits.symm
  change s3.outputTape.bits = finished.inputTape.bits at same
  exact same.trans hResult
  have hSameTape := e3.2.2.2.symm
  change s3.outputTape.Equivalent finished.inputTape at hSameTape
  exact hSameTape.trans hFinishLayout


/-- Every raw bitstring terminates within the usual quartic budget when
caller data are separated from it by a blank input cell. -/
theorem runs_with_saved (input : List Bool) (before : List (Option Bool)) :
    ∃ (output : List Bool) (target : Configuration) (used blanks : Nat),
      output.length ≤ input.length ∧ used ≤ budget input.length ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits input with left := none :: before } } : Configuration) target used ∧
      target.halted = true ∧ target.outputBits = output ∧
      target.outputTape.Equivalent
        { left := output.reverse.map some ++ [none], right := List.replicate blanks none } := by
  obtain ⟨rawColumns, initialized, hWidth, hInitHalt, hInitInput, hInitOutput, hInitEval⟩ :=
    BinaryProductInitialization.complete_matrix_context input (none :: before)
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, _, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput⟩ :=
    BinaryProductLoop.runs (initialColumns rawColumns) (input.reverse.map some ++ none :: before)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, hLayout⟩ := runs_from_components_saved input (none :: before) rawColumns initialized
    hWidth hInitHalt hInitInput hInitOutput hInitEval finalColumns finalSaved loopTarget loopSteps
    hFinalWidth hLoopBound loopRun hLoopHalt hLoopInput hLoopOutput
  refine ⟨finalColumns.map Column.accumulator, target, used,
    (matrix finalColumns).length - finalColumns.length, ?_, hUsed, native, hHalt,
    hOutput, hLayout⟩
  simpa only [List.length_map, hFinalWidth, initialColumns] using hWidth

theorem runs_with_layout (input : List Bool) :
    ∃ (output : List Bool) (target : Configuration) (used blanks : Nat),
      output.length ≤ input.length ∧ used ≤ budget input.length ∧
      RunsFor program (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = output ∧
      target.outputTape.Equivalent
        { left := output.reverse.map some ++ [none], right := List.replicate blanks none } := by
  obtain ⟨rawColumns, initialized, hWidth, hInitHalt, hInitInput, hInitOutput, hInitEval⟩ :=
    BinaryProductInitialization.complete_matrix input
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, _, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput⟩ :=
    BinaryProductLoop.runs (initialColumns rawColumns) (input.reverse.map some)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, hLayout⟩ := runs_from_components input rawColumns initialized
    hWidth hInitHalt hInitInput hInitOutput hInitEval finalColumns finalSaved loopTarget loopSteps
    hFinalWidth hLoopBound loopRun hLoopHalt hLoopInput hLoopOutput
  refine ⟨finalColumns.map Column.accumulator, target, used,
    (matrix finalColumns).length - finalColumns.length, ?_, hUsed, native, hHalt,
    hOutput, hLayout⟩
  simpa only [List.length_map, hFinalWidth, initialColumns] using hWidth

/-- The original output-only projection remains available. -/
theorem runs (input : List Bool) :
    ∃ (output : List Bool) (target : Configuration) (used : Nat),
      output.length ≤ input.length ∧ used ≤ budget input.length ∧
      RunsFor program (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = output := by
  obtain ⟨output, target, used, _, hLength, hUsed, run, hHalt, hOutput, _⟩ :=
    runs_with_layout input
  exact ⟨output, target, used, hLength, hUsed, run, hHalt, hOutput⟩

theorem haltsWithin (input : List Bool) : HaltsWithin program input (budget input.length) := by
  obtain ⟨_, target, used, _, hUsed, native, hHalt, _⟩ := runs input
  exact native.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, (PolynomiallyBounded.const 1000000).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow 4), haltsWithin⟩

end Machine.BinaryProductProgram
