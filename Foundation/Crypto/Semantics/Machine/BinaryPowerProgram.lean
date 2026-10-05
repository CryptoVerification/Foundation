import Foundation.Crypto.Semantics.Machine.BinaryPowerLoop
import Foundation.Crypto.Semantics.Machine.BinaryPowerSeed
import Foundation.Crypto.Semantics.Machine.BinaryProductFinalization

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinaryPowerProgram

open BinaryProductSelection

private def initialization : Program := BinaryProductInitialization.program.asSubroutine 0 120
private def seedExit : Nat := 120 + BinaryPowerSeed.program.length + 1
private def beforeLoop : Program := initialization ++
  BinaryPowerSeed.program.swapTapes.asSubroutine 120 (seedExit + 3)
private def loopExit (loop : Program) : Nat :=
  (beforeLoop ++ loop.swapTapes.asSubroutine seedExit 0).length
private def beforeFinish (loop : Program) : Program := beforeLoop ++
  loop.swapTapes.asSubroutine seedExit (loopExit loop)
private def finishExit (loop : Program) : Nat :=
  (beforeFinish loop).length + BinaryProductFinalization.program.swapTapes.length + 1

private def programWithLoop (loop : Program) : Program :=
  Program.withSubroutine (beforeFinish loop)
    BinaryProductFinalization.program.swapTapes [.halt] (finishExit loop)

/-- One finite bit-machine program initializes a five-track matrix, writes
its power accumulator to one, consumes exponent flags by squaring and
conditional multiplication, and copies the final bits to the output tape. -/
def program : Program := programWithLoop BinaryPowerLoop.program

def budget (length : Nat) : Nat :=
  100000000000000000000000 * (length + 1) ^ 10

private theorem initialization_length : initialization.length = 120 := by
  simp [initialization, show BinaryProductInitialization.program.length = 119 from rfl]
private theorem beforeLoop_length : beforeLoop.length = seedExit := by
  simp only [beforeLoop, List.length_append, Program.asSubroutine_length,
    Program.swapTapes_length, initialization_length, seedExit]
  omega
private theorem beforeFinish_length (loop : Program) : (beforeFinish loop).length = loopExit loop := by
  change (beforeLoop ++ loop.swapTapes.asSubroutine seedExit (loopExit loop)).length =
    (beforeLoop ++ loop.swapTapes.asSubroutine seedExit 0).length
  simp only [List.length_append, Program.asSubroutine_length]

private theorem initialization_layout (loop : Program) : programWithLoop loop = Program.withSubroutine []
    BinaryProductInitialization.program
    (BinaryPowerSeed.program.swapTapes.asSubroutine 120 (seedExit + 3) ++
      loop.swapTapes.asSubroutine seedExit (loopExit loop) ++
      BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt]) 120 := by
  simp only [programWithLoop, Program.withSubroutine, beforeFinish_length]
  simp [beforeFinish, beforeLoop, initialization, Program.withSubroutine, List.append_assoc]

private theorem seed_layout (loop : Program) : programWithLoop loop = Program.withSubroutine initialization
    BinaryPowerSeed.program.swapTapes
    (loop.swapTapes.asSubroutine seedExit (loopExit loop) ++
      BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt])
    (seedExit + 3) := by
  simp only [programWithLoop, Program.withSubroutine, beforeFinish_length, initialization_length]
  simp [beforeFinish, beforeLoop, List.append_assoc]

private theorem loop_layout (loop : Program) : programWithLoop loop = Program.withSubroutine beforeLoop
    loop.swapTapes
    (BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt])
    (loopExit loop) := by
  simp only [programWithLoop, Program.withSubroutine, beforeFinish_length, beforeLoop_length]
  simp [beforeFinish, List.append_assoc]

private theorem no_randomBit_for (loop : Program)
    (hLoop : ∀ tape, Instruction.randomBit tape ∉ loop)
    (tape : TapeId) : Instruction.randomBit tape ∉ programWithLoop loop := by
  simp only [programWithLoop, Program.withSubroutine, beforeFinish, beforeLoop, initialization,
    List.mem_append, not_or]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, by simp⟩
  · exact Program.asSubroutine_no_randomBit _ BinaryProductInitialization.no_randomBit _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ BinaryPowerSeed.no_randomBit) _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ hLoop) _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ BinaryProductFinalization.no_randomBit) _ _ tape

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  no_randomBit_for BinaryPowerLoop.program BinaryPowerLoop.no_randomBit tape

private theorem final_halt_lookup (front source : Program) (returnPc : Nat) :
    (Program.withSubroutine front source [.halt] returnPc)[front.length + source.length + 1]? =
      some .halt := by
  have lookup := Program.withSubroutine_getElem?_suffix front source [.halt] returnPc 0
  simpa only [Nat.add_zero, List.getElem?_cons_zero] using lookup

private theorem step_halt (source : Program) (s : Configuration)
    (ha : s.halted = false) (lookup : source[s.pc]? = some .halt) :
    Step source s { s with halted := true } := by
  simp [Step, successors, next, ha, lookup, Instruction.next]

/-- Native linking theorem for the charged initialization, seed, exponent
loop and final output. The intermediate matrix stays on physical tapes. -/
theorem runs_from_components (loop : Program) (hEntry : 3 ≤ loop.length)
    (input : List Bool)
    (rawColumns : List BinaryModularAddition.Column) (initialized : Configuration)
    (hWidth : rawColumns.length ≤ input.length) (hInitHalt : initialized.halted = true)
    (hInitInput : initialized.inputTape = { left := input.reverse.map some })
    (hInitOutput : initialized.outputTape = { left := (BinaryProductInitialization.matrix rawColumns).reverse.map some })
    (hInitEval : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * (input.length + 1)) = PMF.pure initialized)
    (finalColumns : List Column) (finalSaved : List (Option Bool))
    (loopTarget : Configuration) (loopSteps : Nat)
    (hFinalWidth : finalColumns.length = (BinaryPowerSeed.seeded (initialColumns rawColumns)).length)
    (hLoopBound : loopSteps ≤ BinaryPowerLoop.budget (BinaryPowerSeed.seeded (initialColumns rawColumns)).length
      (pendingCount (BinaryPowerSeed.seeded (initialColumns rawColumns))))
    (loopRun : RunsFor loop
      (BinaryPowerLoop.start (BinaryPowerSeed.seeded (initialColumns rawColumns)) (input.reverse.map some))
      loopTarget loopSteps)
    (hLoopHalt : loopTarget.halted = true)
    (hLoopInput : loopTarget.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] })
    (hLoopOutput : loopTarget.outputTape.Equivalent { left := finalSaved }) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget input.length ∧
      RunsFor (programWithLoop loop) (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = finalColumns.map Column.accumulator ∧
      target.outputTape.Equivalent
        { left := (finalColumns.map Column.accumulator).reverse.map some ++ [none],
          right := List.replicate ((matrix finalColumns).length - finalColumns.length) none } := by
  obtain ⟨s1, u1, hu1, r1, e1⟩ := nativeCall_of_eval [] BinaryProductInitialization.program
    (BinaryPowerSeed.program.swapTapes.asSubroutine 120 (seedExit + 3) ++
      loop.swapTapes.asSubroutine seedExit (loopExit loop) ++
      BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt]) 120
    (Configuration.initial input) initialized (Configuration.initial input) (17 * (input.length + 1))
    (by change 0 ≤ _; omega) rfl hInitHalt hInitEval (Configuration.Equivalent.refl _)
  rw [← initialization_layout loop] at r1
  let columns := initialColumns rawColumns
  let seeded := BinaryPowerSeed.seeded columns
  let saved := input.reverse.map some
  obtain ⟨seedTarget, seedSteps, seedBound, seedRun, seedHalt, seedInput, seedOutput⟩ :=
    BinaryPowerSeed.runs columns saved
  have seedLayout : (((BinaryPowerSeed.start columns saved).swapTapes).rebasePc
      initialization.length).Equivalent s1 := by
    refine ⟨?_, e1.2.1, ?_, ?_⟩
    · change initialization.length + 0 = s1.pc
      rw [initialization_length, Nat.add_zero]
      exact e1.1
    · have same := e1.2.2.1
      change initialized.inputTape.Equivalent s1.inputTape at same
      rw [hInitInput] at same
      exact same
    · have same := e1.2.2.2
      change initialized.outputTape.Equivalent s1.outputTape at same
      rw [hInitOutput] at same
      simpa only [columns, BinaryPowerSeed.start, initialColumns_matrix,
        Configuration.rebasePc, Configuration.swapTapes] using same
  obtain ⟨u2, hu2, embeddedSeed⟩ := seedRun.swapTapes.withSubroutine_halted initialization
    BinaryPowerSeed.program.swapTapes
    (loop.swapTapes.asSubroutine seedExit (loopExit loop) ++
      BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt])
    (seedExit + 3) (by change 0 ≤ _; omega) rfl seedHalt
  obtain ⟨s2, r2, e2⟩ := embeddedSeed.exists_equivalent seedLayout
  rw [← seed_layout loop] at r2
  have loopLayout : (((BinaryPowerLoop.start seeded saved).swapTapes).rebasePc
      beforeLoop.length).Equivalent s2 := by
    refine ⟨?_, e2.2.1, ?_, ?_⟩
    · change beforeLoop.length + 3 = s2.pc
      rw [beforeLoop_length]
      exact e2.1
    · exact seedOutput.symm.trans e2.2.2.1
    · exact seedInput.symm.trans e2.2.2.2
  obtain ⟨u3, hu3, embeddedLoop⟩ := loopRun.swapTapes.withSubroutine_halted beforeLoop
    loop.swapTapes
    (BinaryProductFinalization.program.swapTapes.asSubroutine (loopExit loop) (finishExit loop) ++ [.halt]) (loopExit loop)
    (by rw [Program.swapTapes_length]; exact hEntry) rfl hLoopHalt
  obtain ⟨s3, r3, e3⟩ := embeddedLoop.exists_equivalent loopLayout
  rw [← loop_layout loop] at r3
  obtain ⟨finished, finishSteps, hFinishBound, finishRun, hFinishHalt, hResult,
    hFinishLayout⟩ :=
    BinaryProductFinalization.runs_with_layout finalColumns finalSaved
  have finishLayout : (((BinaryProductFinalization.start finalColumns finalSaved).swapTapes).rebasePc
      (beforeFinish loop).length).Equivalent s3 := by
    refine ⟨?_, e3.2.1, ?_, ?_⟩
    · change (beforeFinish loop).length + 0 = s3.pc
      rw [beforeFinish_length loop, Nat.add_zero]
      exact e3.1
    · exact hLoopOutput.symm.trans e3.2.2.1
    · exact hLoopInput.symm.trans e3.2.2.2
  obtain ⟨u4, hu4, embeddedFinish⟩ := finishRun.swapTapes.withSubroutine_halted (beforeFinish loop)
    BinaryProductFinalization.program.swapTapes [.halt] (finishExit loop)
    (by change 0 ≤ _; omega) rfl hFinishHalt
  obtain ⟨s4, r4, e4⟩ := embeddedFinish.exists_equivalent finishLayout
  have lookup : (programWithLoop loop)[finishExit loop]? = some .halt := by
    have hProgram : programWithLoop loop = Program.withSubroutine (beforeFinish loop)
        BinaryProductFinalization.program.swapTapes [.halt] (finishExit loop) := rfl
    have hIndex : (finishExit loop) = (beforeFinish loop).length +
        BinaryProductFinalization.program.swapTapes.length + 1 := rfl
    calc
      (programWithLoop loop)[finishExit loop]? =
          (Program.withSubroutine (beforeFinish loop) BinaryProductFinalization.program.swapTapes
            [.halt] (finishExit loop))[finishExit loop]? :=
        congrArg (fun source : Program => source[finishExit loop]?) hProgram
      _ = some .halt := by rw [hIndex]; exact final_halt_lookup _ _ _
  have last : Step (programWithLoop loop) s4 { s4 with halted := true } := by
    have hp : s4.pc = finishExit loop := e4.1.symm
    have ha : s4.halted = false := e4.2.1.symm
    have atPc : (programWithLoop loop)[s4.pc]? = some .halt := by rw [hp]; exact lookup
    exact step_halt (programWithLoop loop) s4 ha atPc
  have hColumns : columns.length = rawColumns.length := by simp [columns, initialColumns]
  have hSeeded : seeded.length = columns.length := BinaryPowerSeed.seeded_length columns
  have hSourceSize : seeded.length ≤ input.length := by omega
  have hSize : finalColumns.length ≤ input.length := hFinalWidth ▸ hSourceSize
  have hCount : pendingCount seeded ≤ seeded.length := List.length_filter_le _ _
  have hWidthBudget : BinaryPowerLoop.budget seeded.length (pendingCount seeded) ≤
      BinaryPowerLoop.widthBudget seeded.length := Nat.mul_le_mul_right _ (Nat.add_le_add_right hCount 1)
  have hNativeBound : u1 + u2 + u3 + u4 + 1 ≤ budget input.length := by
    have hPoly := BinaryPowerLoop.widthBudget_le seeded.length
    have hPow : (seeded.length + 1) ^ 10 ≤ (input.length + 1) ^ 10 :=
      Nat.pow_le_pow_left (by omega) _
    have hLinear : input.length + 1 ≤ (input.length + 1) ^ 10 :=
      le_self_pow (by omega) (by decide)
    have hLoop : u3 ≤ 2000000000000000000100 * (input.length + 1) ^ 10 :=
      hu3.trans (hLoopBound.trans (hWidthBudget.trans (hPoly.trans (Nat.mul_le_mul_left _ hPow))))
    have hSeed : u2 ≤ 25 * input.length + 8 := by omega
    have hFinish : u4 ≤ 58 * input.length + 15 := by
      have h := hu4.trans hFinishBound
      dsimp only [BinaryProductFinalization.budget] at h
      omega
    dsimp only [budget]
    omega
  refine ⟨{ s4 with halted := true }, u1 + u2 + u3 + u4 + 1,
    hNativeBound, (((r1.trans r2).trans r3).trans r4).succ last, rfl, ?_, ?_⟩
  have same := e4.2.2.2.bits.symm
  change s4.outputTape.bits = finished.inputTape.bits at same
  exact same.trans hResult
  have hSameTape := e4.2.2.2.symm
  change s4.outputTape.Equivalent finished.inputTape at hSameTape
  exact hSameTape.trans hFinishLayout

theorem runs_with_layout (input : List Bool) :
    ∃ (output : List Bool) (target : Configuration) (used blanks : Nat),
      output.length ≤ input.length ∧ used ≤ budget input.length ∧
      RunsFor program (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = output ∧
      target.outputTape.Equivalent
        { left := output.reverse.map some ++ [none],
          right := List.replicate blanks none } := by
  obtain ⟨rawColumns, initialized, hWidth, hInitHalt, hInitInput, hInitOutput, hInitEval⟩ :=
    BinaryProductInitialization.complete_matrix input
  let seeded := BinaryPowerSeed.seeded (initialColumns rawColumns)
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, _, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput⟩ :=
    BinaryPowerLoop.runs seeded (input.reverse.map some)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, hLayout⟩ :=
    runs_from_components BinaryPowerLoop.program BinaryPowerLoop.entry_in_range input
      rawColumns initialized hWidth hInitHalt hInitInput hInitOutput hInitEval
      finalColumns finalSaved loopTarget loopSteps hFinalWidth hLoopBound loopRun
      hLoopHalt hLoopInput hLoopOutput
  refine ⟨finalColumns.map Column.accumulator, target, used,
    (matrix finalColumns).length - finalColumns.length, ?_, hUsed, native, hHalt,
    hOutput, hLayout⟩
  simpa only [List.length_map, hFinalWidth, seeded, BinaryPowerSeed.seeded_length,
    initialColumns, List.length_map] using hWidth

/-- All finite raw three-track inputs terminate, including incomplete
columns and invalid numerical moduli. -/
theorem runs (input : List Bool) :
    ∃ (output : List Bool) (target : Configuration) (used : Nat),
      output.length ≤ input.length ∧ used ≤ budget input.length ∧
      RunsFor program (Configuration.initial input) target used ∧
      target.halted = true ∧ target.outputBits = output := by
  obtain ⟨output, target, used, _, hLength, hUsed, native, hHalt, hOutput, _⟩ :=
    runs_with_layout input
  exact ⟨output, target, used, hLength, hUsed, native, hHalt, hOutput⟩

theorem haltsWithin (input : List Bool) : HaltsWithin program input (budget input.length) := by
  obtain ⟨_, target, used, _, hUsed, native, hHalt, _⟩ := runs input
  exact native.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, (PolynomiallyBounded.const 100000000000000000000000).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow 10), haltsWithin⟩

end Machine.BinaryPowerProgram
