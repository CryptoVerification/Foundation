import Foundation.Machine.BinaryProductGather
import Foundation.Machine.BinaryProductWriteback
import Foundation.Machine.NativeInvocation
import Foundation.Machine.BinaryDoubleReduction

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinaryProductPhase

open BinaryProductSelection BinaryProductWorkspace GuardedCompiler

private def rewindPre : Program := rewindBitstring.asSubroutine 0 5
private def gatherPre : Program := rewindPre ++ [.moveRight .output]
private def gatherEnd (gather : Program) : Nat := 6 + gather.length + 1
private def inputPre (gather : Program) : Program :=
  gatherPre ++ gather.asSubroutine 6 (gatherEnd gather)
private def rewindOutputPre (gather : Program) : Program := inputPre gather ++ [.moveRight .input]
private def kernelEntry (gather : Program) : Nat := gatherEnd gather + 6
private def kernelPre (gather : Program) : Program :=
  rewindOutputPre gather ++ rewindBitstring.swapTapes.asSubroutine
    (gatherEnd gather + 1) (kernelEntry gather)
private def resultEntry (gather kernel : Program) : Nat :=
  kernelEntry gather + (rawCompileOpposite kernel).length + 1
private def resultPre (gather kernel : Program) : Program :=
  kernelPre gather ++ (rawCompileOpposite kernel).asSubroutine
    (kernelEntry gather) (resultEntry gather kernel)
def finalEntry (gather kernel : Program) : Nat :=
  resultEntry gather kernel + BinaryProductWriteback.program.length + 1

/-- One arithmetic phase on the physically retained product matrix.
Rewind, input gathering, guarded invocation, result copy/erasure and
accumulator writes all belong to this one finite native program. -/
def program (gather kernel : Program) : Program :=
  Program.withSubroutine (resultPre gather kernel) BinaryProductWriteback.program [.halt]
    (finalEntry gather kernel)

def start (columns : List Column) (saved : List (Option Bool)) : Configuration :=
  { inputTape := { left := (matrix columns).reverse.map some ++ [none] },
    outputTape := { left := saved } }

def budget (gatherSteps width : Nat) (kernelBudget : Nat → Nat) (requestLength : Nat) : Nat :=
  10 * width + 4 + 1 + gatherSteps + 1 + 2 * requestLength + 4 +
    rawTraceBudget kernelBudget requestLength + BinaryProductWriteback.budget width + 1

private theorem gatherPre_length : gatherPre.length = 6 := by
  simp [gatherPre, rewindPre, show rewindBitstring.length = 4 from rfl]
private theorem inputPre_length (gather : Program) : (inputPre gather).length = gatherEnd gather := by
  simp [inputPre, gatherPre_length, gatherEnd, Nat.add_assoc]
private theorem rewindOutputPre_length (gather : Program) :
    (rewindOutputPre gather).length = gatherEnd gather + 1 := by
  simp [rewindOutputPre, inputPre_length]
private theorem kernelPre_length (gather : Program) : (kernelPre gather).length = kernelEntry gather := by
  simp [kernelPre, rewindOutputPre_length, kernelEntry, show rewindBitstring.length = 4 from rfl]
private theorem resultPre_length (gather kernel : Program) :
    (resultPre gather kernel).length = resultEntry gather kernel := by
  simp [resultPre, kernelPre_length, resultEntry, Nat.add_assoc]

private theorem cells_append_blanks (cells : List (Option Bool)) (blanks i : Nat) :
    (cells ++ List.replicate blanks none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => exact (Tape.blank_padding_equivalent [] blanks).2.2 i
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

private theorem call (gather kernel pre source suffix : Program) (returnPc : Nat)
    (layout : program gather kernel = Program.withSubroutine pre source suffix returnPc)
    (canonical returned actual : Configuration) (limit : Nat)
    (hPc : canonical.pc ≤ source.length) (hActive : canonical.halted = false)
    (hHalted : returned.halted = true)
    (hEval : evalConfigWithin source canonical limit = PMF.pure returned)
    (hLayout : (canonical.rebasePc pre.length).Equivalent actual) :
    ∃ (target : Configuration) (used : Nat), used ≤ limit ∧
      RunsFor (program gather kernel) actual target used ∧ (returned.resumeAt returnPc).Equivalent target := by
  obtain ⟨target, used, hUsed, hRun, hTarget⟩ := nativeCall_of_eval pre source suffix returnPc
    canonical returned actual limit hPc hActive hHalted hEval hLayout
  rw [← layout] at hRun
  exact ⟨target, used, hUsed, hRun, hTarget⟩

private theorem prefix_layout (gather kernel : Program) :
    program gather kernel = rewindPre ++ [.moveRight .output] ++
      gather.asSubroutine 6 (gatherEnd gather) ++ [.moveRight .input] ++
      rewindBitstring.swapTapes.asSubroutine (gatherEnd gather + 1) (kernelEntry gather) ++
      (rawCompileOpposite kernel).asSubroutine (kernelEntry gather) (resultEntry gather kernel) ++
      BinaryProductWriteback.program.asSubroutine (resultEntry gather kernel) (finalEntry gather kernel) ++ [.halt] := by
  simp only [program, Program.withSubroutine, resultPre_length]
  simp [resultPre, kernelPre, rewindOutputPre, inputPre, gatherPre, List.append_assoc]

/-- The statement includes the native input preparer's full returned
configuration. The request is consequently produced by actual tape writes;
it is never supplied to the arithmetic call by a free fresh-input reload. -/
theorem runs_after_rewind (gather kernel : Program) (columns : List Column)
    (request result : List Bool) (saved : List (Option Bool))
    (gatherSteps : Nat) (kernelBudget : Nat → Nat)
    (input : Tape) (rewound : Configuration) (rewindSteps : Nat)
    (hRewindBound : rewindSteps ≤ 10 * columns.length + 4)
    (hRewind : RunsFor rewindBitstring
      { inputTape := input, outputTape := { left := saved } } rewound rewindSteps)
    (hRewindLayout : rewound.Equivalent
      { pc := 3, inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := saved }, halted := true })
    (hResultLength : result.length = columns.length)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ kernel)
    (hKernelHalt : HaltsWithin kernel request (kernelBudget request.length))
    (hKernelCorrect : evalWithin kernel request (kernelBudget request.length) = PMF.pure (some result))
    (hGather : evalConfigWithin gather
      { inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := none :: saved } } gatherSteps =
      PMF.pure {
        pc := gather.length - 1,
        inputTape := { left := (matrix columns).reverse.map some ++ [none] },
        outputTape := { left := request.reverse.map some ++ none :: saved }, halted := true }) :
    ∃ (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      used ≤ budget gatherSteps columns.length kernelBudget request.length ∧
      RunsFor (program gather kernel)
        { inputTape := input, outputTape := { left := saved } } target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } := by
  let mat := matrix columns
  let suffix1 := [.moveRight .output] ++ gather.asSubroutine 6 (gatherEnd gather) ++
    [.moveRight .input] ++ rewindBitstring.swapTapes.asSubroutine (gatherEnd gather + 1) (kernelEntry gather) ++
    (rawCompileOpposite kernel).asSubroutine (kernelEntry gather) (resultEntry gather kernel) ++
    BinaryProductWriteback.program.asSubroutine (resultEntry gather kernel) (finalEntry gather kernel) ++ [.halt]
  have layout1 : program gather kernel = Program.withSubroutine [] rewindBitstring suffix1 5 := by
    rw [prefix_layout]
    simp [Program.withSubroutine, rewindPre, suffix1, List.append_assoc]
  obtain ⟨s1, u1, hu1, r1, e1⟩ := call gather kernel [] rewindBitstring suffix1 5 layout1
    { inputTape := input, outputTape := { left := saved } } rewound
    { inputTape := input, outputTape := { left := saved } }
    rewindSteps (by change 0 ≤ _; omega) rfl hRewindLayout.2.1
    (hRewind.evalConfigWithin_eq_pure_of_no_randomBit rewindBitstring_no_randomBit)
    (Configuration.Equivalent.refl _)
  let moved : Configuration := { s1 with pc := 6, outputTape := s1.outputTape.moveRight }
  have moveOutput : Step (program gather kernel) s1 moved := by
    have hp : s1.pc = 5 := e1.1.symm
    have ha : s1.halted = false := e1.2.1.symm
    have hi : (program gather kernel)[5]? = some (.moveRight .output) := by
      rw [prefix_layout]
      simp [rewindPre, Program.asSubroutine, rewindBitstring]
    simp [Step, successors, next, hp, ha, hi, moved, Instruction.next,
      Configuration.advance, Configuration.updateTape]
  let gatherStart : Configuration :=
    { inputTape := { Tape.ofBits mat with left := [none] }, outputTape := { left := none :: saved } }
  let gatherFinish : Configuration :=
    { pc := gather.length - 1, inputTape := { left := mat.reverse.map some ++ [none] },
      outputTape := { left := request.reverse.map some ++ none :: saved }, halted := true }
  let suffix2 := [.moveRight .input] ++
    rewindBitstring.swapTapes.asSubroutine (gatherEnd gather + 1) (kernelEntry gather) ++
    (rawCompileOpposite kernel).asSubroutine (kernelEntry gather) (resultEntry gather kernel) ++
    BinaryProductWriteback.program.asSubroutine (resultEntry gather kernel) (finalEntry gather kernel) ++ [.halt]
  have layout2 : program gather kernel = Program.withSubroutine gatherPre gather suffix2 (gatherEnd gather) := by
    rw [prefix_layout]
    simp [Program.withSubroutine, gatherPre, rewindPre,
      show rewindBitstring.length = 4 from rfl, suffix2, List.append_assoc]
  have gatherLayout : (gatherStart.rebasePc gatherPre.length).Equivalent moved := by
    refine ⟨by rw [gatherPre_length]; rfl, e1.2.1, ?_, ?_⟩
    · exact hRewindLayout.2.2.1.symm.trans e1.2.2.1
    · exact (hRewindLayout.2.2.2.symm.trans e1.2.2.2).moveRight
  obtain ⟨s2, u2, hu2, r2, e2⟩ := call gather kernel gatherPre gather suffix2 (gatherEnd gather) layout2
    gatherStart gatherFinish moved gatherSteps (by change 0 ≤ _; omega) rfl rfl hGather gatherLayout
  let inputMoved : Configuration := { s2 with pc := gatherEnd gather + 1, inputTape := s2.inputTape.moveRight }
  have moveInput : Step (program gather kernel) s2 inputMoved := by
    have hp : s2.pc = gatherEnd gather := e2.1.symm
    have ha : s2.halted = false := e2.2.1.symm
    have hi : (program gather kernel)[gatherEnd gather]? = some (.moveRight .input) := by
      rw [layout2]
      have lookup := Program.withSubroutine_getElem?_suffix gatherPre gather suffix2 (gatherEnd gather) 0
      change _ = some (Instruction.moveRight TapeId.input) at lookup
      simpa only [gatherPre_length, gatherEnd, Nat.add_zero] using lookup
    simp [Step, successors, next, hp, ha, hi, inputMoved, Instruction.next,
      Configuration.advance, Configuration.updateTape]
  let matrixEnd : Tape := { left := none :: mat.reverse.map some ++ [none] }
  let suffix3 := (rawCompileOpposite kernel).asSubroutine (kernelEntry gather) (resultEntry gather kernel) ++
    BinaryProductWriteback.program.asSubroutine (resultEntry gather kernel) (finalEntry gather kernel) ++ [.halt]
  have layout3 : program gather kernel = Program.withSubroutine (rewindOutputPre gather)
      rewindBitstring.swapTapes suffix3 (kernelEntry gather) := by
    rw [prefix_layout]
    simp only [Program.withSubroutine, rewindOutputPre_length]
    simp [rewindOutputPre, inputPre, gatherPre, suffix3, List.append_assoc]
  have rewindOutputEval := (rewindScratch_runs saved request matrixEnd).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit
      (Program.swapTapes_no_randomBit rewindBitstring rewindBitstring_no_randomBit)
  have rewindOutputLayout :
      ((rewindScratchStart saved request matrixEnd).swapTapes.rebasePc (rewindOutputPre gather).length).Equivalent inputMoved := by
    refine ⟨by rw [rewindOutputPre_length]; rfl, e2.2.1, ?_, ?_⟩
    · exact e2.2.2.1.moveRight
    · exact e2.2.2.2
  obtain ⟨s3, u3, hu3, r3, e3⟩ := call gather kernel (rewindOutputPre gather)
    rewindBitstring.swapTapes suffix3 (kernelEntry gather) layout3
    (rewindScratchStart saved request matrixEnd).swapTapes
    (rewindScratchFinish saved request matrixEnd).swapTapes inputMoved (2 * request.length + 4)
    (by change 0 ≤ _; omega) rfl rfl rewindOutputEval rewindOutputLayout
  obtain ⟨c, hcHalt, hcOutput, kernelEval⟩ := rawCompileOpposite_result kernel request result
    (none :: saved) (none :: mat.reverse.map some ++ [none]) kernelBudget hNoRandom hKernelHalt hKernelCorrect
  have hcBits : c.outputTape.bits = result := hcOutput
  let returned := (rawResultFrom kernel request (none :: saved) (none :: mat.reverse.map some ++ [none]) c).swapTapes
  let suffix4 := BinaryProductWriteback.program.asSubroutine (resultEntry gather kernel) (finalEntry gather kernel) ++ [.halt]
  have layout4 : program gather kernel = Program.withSubroutine (kernelPre gather)
      (rawCompileOpposite kernel) suffix4 (resultEntry gather kernel) := by
    rw [prefix_layout]
    simp only [Program.withSubroutine, kernelPre_length]
    simp [kernelPre, rewindOutputPre, inputPre, gatherPre, suffix4, List.append_assoc]
  have kernelLayout :
      ((packInputStart (none :: saved) (none :: mat.reverse.map some ++ [none]) request).swapTapes.rebasePc
        (kernelPre gather).length).Equivalent s3 := by
    refine ⟨?_, e3.2.1, e3.2.2.1, ?_⟩
    · rw [kernelPre_length]; exact e3.1
    · have hScratch : (rewindScratchFinish saved request matrixEnd).inputTape.Equivalent
          { Tape.ofBits request with left := none :: saved } := by
        cases request with
        | nil => exact Tape.Equivalent.refl _
        | cons bit rest =>
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro i
          change (rest.map some ++ [none]).getD i none = (rest.map some).getD i none
          simpa only [List.replicate_one] using cells_append_blanks (rest.map some) 1 i
      exact hScratch.symm.trans e3.2.2.2
  obtain ⟨s4, u4, hu4, r4, e4⟩ := call gather kernel (kernelPre gather) (rawCompileOpposite kernel)
    suffix4 (resultEntry gather kernel) layout4
    (packInputStart (none :: saved) (none :: mat.reverse.map some ++ [none]) request).swapTapes
    returned s3 (rawTraceBudget kernelBudget request.length) (by change 0 ≤ _; omega) rfl rfl kernelEval kernelLayout
  let retained := returned.outputTape.left
  have writebackLayout : ((BinaryProductWriteback.start columns result retained).rebasePc
      (resultPre gather kernel).length).Equivalent s4 := by
    refine ⟨?_, e4.2.1, ?_, ?_⟩
    · rw [resultPre_length]; exact e4.1
    · have hInput : (BinaryProductWriteback.start columns result retained).inputTape.Equivalent returned.inputTape := by
        simp only [returned, rawResultFrom, Configuration.swapTapes, extractOutputFinish,
          copyScratchFinish, hcBits, BinaryProductWriteback.start]
        refine ⟨rfl, ?_, ?_⟩
        · intro i
          simpa only [List.append_assoc, List.cons_append, List.map_reverse, List.replicate_one, mat] using
            (cells_append_blanks (result.reverse.map some ++ none :: mat.reverse.map some) 1 i).symm
        · intro i
          exact (Tape.blank_padding_equivalent [] _).symm.2.2 i
      exact hInput.trans e4.2.2.1
    · exact e4.2.2.2
  obtain ⟨written, writeSteps, hWriteSteps, writeRun, writeEquivalent⟩ :=
    BinaryProductWriteback.runs columns result hResultLength retained
  obtain ⟨used5, hUsed5, embedded⟩ := writeRun.withSubroutine_halted
    (resultPre gather kernel) BinaryProductWriteback.program [.halt] (finalEntry gather kernel)
    (by change 0 ≤ _; omega) rfl writeEquivalent.2.1.symm
  change RunsFor (program gather kernel)
    ((BinaryProductWriteback.start columns result retained).rebasePc (resultPre gather kernel).length)
    (written.resumeAt (finalEntry gather kernel)) used5 at embedded
  obtain ⟨s5, r5, e5⟩ := embedded.exists_equivalent writebackLayout
  have hLast : Step (program gather kernel) s5 { s5 with halted := true } := by
    have hp : s5.pc = finalEntry gather kernel := e5.1.symm
    have ha : s5.halted = false := e5.2.1.symm
    have hi : (program gather kernel)[finalEntry gather kernel]? = some .halt := by
      change (Program.withSubroutine (resultPre gather kernel) BinaryProductWriteback.program [.halt]
        (finalEntry gather kernel))[finalEntry gather kernel]? = some .halt
      rw [show finalEntry gather kernel = (resultPre gather kernel).length +
        BinaryProductWriteback.program.length + 1 + 0 by
          simp [finalEntry, resultPre_length],
        Program.withSubroutine_getElem?_suffix]
      rfl
    simp [Step, successors, next, hp, ha, hi, Instruction.next]
  have native := ((((r1.succ moveOutput).trans r2).succ moveInput).trans r3).trans r4 |>.trans r5
  refine ⟨{ s5 with halted := true }, u1 + 1 + u2 + 1 + u3 + u4 + used5 + 1,
    retained, ?_, RunsFor.succ native hLast, rfl, ?_, ?_⟩
  · have hMat : mat.length = 5 * columns.length := by
      simp [mat, matrix, row, List.length_flatMap, Nat.mul_comm]
    dsimp only [budget]
    omega
  · exact (writeEquivalent.2.2.1.trans e5.2.2.1).symm
  · exact (writeEquivalent.2.2.2.trans e5.2.2.2).symm

theorem runs (gather kernel : Program) (columns : List Column)
    (request result : List Bool) (saved : List (Option Bool))
    (gatherSteps : Nat) (kernelBudget : Nat → Nat)
    (hResultLength : result.length = columns.length)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ kernel)
    (hKernelHalt : HaltsWithin kernel request (kernelBudget request.length))
    (hKernelCorrect : evalWithin kernel request (kernelBudget request.length) = PMF.pure (some result))
    (hGather : evalConfigWithin gather
      { inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := none :: saved } } gatherSteps =
      PMF.pure {
        pc := gather.length - 1,
        inputTape := { left := (matrix columns).reverse.map some ++ [none] },
        outputTape := { left := request.reverse.map some ++ none :: saved }, halted := true }) :
    ∃ (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      used ≤ budget gatherSteps columns.length kernelBudget request.length ∧
      RunsFor (program gather kernel) (start columns saved) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } := by
  have layout : (rewindScratchFinish [] (matrix columns) { left := saved }).Equivalent
      { pc := 3, inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := saved }, halted := true } := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    cases hMatrix : matrix columns with
    | nil => exact Tape.Equivalent.refl _
    | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      change (rest.map some ++ [none]).getD i none = (rest.map some).getD i none
      simpa only [List.replicate_one] using cells_append_blanks (rest.map some) 1 i
  exact runs_after_rewind gather kernel columns request result saved gatherSteps kernelBudget
    _ _ (2 * (matrix columns).length + 4)
    (by simp [matrix, row, List.length_flatMap, Nat.mul_comm]; omega)
    (rewindScratch_runs [] (matrix columns) { left := saved }) layout
    hResultLength hNoRandom hKernelHalt hKernelCorrect hGather

/-- The arithmetic phase also accepts the actual interior head position
left by bit selection. Its first native rewind scans only the represented
prefix and preserves the unvisited suffix of the same physical matrix. -/
theorem runs_from_split (gather kernel : Program) (columns : List Column)
    (leading remaining request result : List Bool) (saved : List (Option Bool))
    (gatherSteps : Nat) (kernelBudget : Nat → Nat)
    (hMatrix : leading ++ remaining = matrix columns)
    (hResultLength : result.length = columns.length)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ kernel)
    (hKernelHalt : HaltsWithin kernel request (kernelBudget request.length))
    (hKernelCorrect : evalWithin kernel request (kernelBudget request.length) = PMF.pure (some result))
    (hGather : evalConfigWithin gather
      { inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := none :: saved } } gatherSteps =
      PMF.pure {
        pc := gather.length - 1,
        inputTape := { left := (matrix columns).reverse.map some ++ [none] },
        outputTape := { left := request.reverse.map some ++ none :: saved }, halted := true }) :
    ∃ (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      used ≤ budget gatherSteps columns.length kernelBudget request.length ∧
      RunsFor (program gather kernel)
        { inputTape := { Tape.ofBits remaining with left := leading.reverse.map some },
          outputTape := { left := saved } } target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } := by
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ right := leading.map some ++ (Tape.ofBits remaining).current ::
        (Tape.ofBits remaining).right } : Tape).moveRight,
      outputTape := { left := saved }, halted := true }
  have hLayout : rewound.Equivalent
      { pc := 3, inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := saved }, halted := true } := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    rw [← hMatrix]
    cases leading with
    | nil => cases remaining <;> exact Tape.Equivalent.refl _
    | cons bit rest =>
      cases remaining with
      | nil =>
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro index
          simpa only [rewound, List.map_cons, Tape.ofBits, Tape.moveRight,
            List.cons_append, List.append_nil, List.replicate_one] using
            cells_append_blanks (rest.map some) 1 index
      | cons next tail =>
          simp only [rewound, List.map_cons, Tape.ofBits, Tape.moveRight,
            List.cons_append, List.map_append]
          exact Tape.Equivalent.refl _
  have hLength : leading.length ≤ 5 * columns.length := by
    have h := congrArg List.length hMatrix
    simp [matrix, row, List.length_flatMap, Nat.mul_comm] at h
    omega
  exact runs_after_rewind gather kernel columns request result saved gatherSteps kernelBudget
    _ rewound (2 * leading.length + 4) (by omega)
    (rewindBitstring_runs_from leading (Tape.ofBits remaining).current (Tape.ofBits remaining).right { left := saved })
    hLayout hResultLength hNoRandom hKernelHalt hKernelCorrect hGather

theorem no_randomBit (gather kernel : Program)
    (hGather : ∀ tape, Instruction.randomBit tape ∉ gather)
    (hKernel : ∀ tape, Instruction.randomBit tape ∉ kernel) (tape : TapeId) :
    Instruction.randomBit tape ∉ program gather kernel := by
  rw [prefix_layout]
  simp only [List.mem_append, not_or]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact Program.asSubroutine_no_randomBit _ rewindBitstring_no_randomBit _ _ tape
  · simp
  · exact Program.asSubroutine_no_randomBit _ hGather _ _ tape
  · simp
  · exact Program.asSubroutine_no_randomBit _
      (Program.swapTapes_no_randomBit _ rewindBitstring_no_randomBit) _ _ tape
  · exact Program.asSubroutine_no_randomBit _ (rawCompileOpposite_no_randomBit _ hKernel) _ _ tape
  · exact Program.asSubroutine_no_randomBit _ BinaryProductWriteback.no_randomBit _ _ tape
  · simp

def doubleProgram : Program := program BinaryProductGather.doubleInputProgram BinaryDoubleReduction.program
def addProgram (selected : Bool) : Program :=
  program (BinaryProductGather.addTriplesProgram selected) BinaryModularAddition.program

def doubleRequest (columns : List Column) : List Bool :=
  false :: BinaryComparison.interleave (columns.map fun column => (column.accumulator, column.modulus))
def addRequest (selected : Bool) (columns : List Column) : List Bool :=
  BinaryModularAddition.interleave (columns.map fun column =>
    ((column.accumulator, if selected then column.operand else false), column.modulus))
def doubleBudget (width : Nat) : Nat :=
  budget (30 * width + 5) width (fun _ => 18 * width + 15) (2 * width + 1)
def addBudget (width : Nat) : Nat :=
  budget (30 * width + 2) width (fun _ => 24 * width + 10) (3 * width)

private theorem affine_polynomiallyBounded (scale offset : Nat) :
    PolynomiallyBounded (fun width => scale * width + offset) :=
  ((PolynomiallyBounded.const scale).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const offset)

private theorem rawBudget_affine_polynomiallyBounded (scale offset requestScale requestOffset : Nat) :
    PolynomiallyBounded (fun width =>
      rawTraceBudget (fun _ => scale * width + offset) (requestScale * width + requestOffset)) := by
  have majorant := ((PolynomiallyBounded.const 125).mul
    ((affine_polynomiallyBounded requestScale requestOffset).add (PolynomiallyBounded.const 1))).mul
      (((affine_polynomiallyBounded scale offset).add (PolynomiallyBounded.const 1)).pow 2)
  exact majorant.mono fun width => rawTraceBudget_bound _ _

theorem doubleBudget_polynomiallyBounded : PolynomiallyBounded doubleBudget := by
  have h := ((((((affine_polynomiallyBounded 10 4).add (PolynomiallyBounded.const 1)).add
    (affine_polynomiallyBounded 30 5)).add (PolynomiallyBounded.const 1)).add
      ((affine_polynomiallyBounded 2 1).mul (PolynomiallyBounded.const 2) |>.add
        (PolynomiallyBounded.const 4))).add
      (rawBudget_affine_polynomiallyBounded 18 15 2 1)).add
        (affine_polynomiallyBounded 40 24) |>.add (PolynomiallyBounded.const 1)
  convert h using 1
  funext width
  simp only [doubleBudget, budget, BinaryProductWriteback.budget]
  ring

theorem addBudget_polynomiallyBounded : PolynomiallyBounded addBudget := by
  have h := ((((((affine_polynomiallyBounded 10 4).add (PolynomiallyBounded.const 1)).add
    (affine_polynomiallyBounded 30 2)).add (PolynomiallyBounded.const 1)).add
      ((affine_polynomiallyBounded 3 0).mul (PolynomiallyBounded.const 2) |>.add
        (PolynomiallyBounded.const 4))).add
      (rawBudget_affine_polynomiallyBounded 24 10 3 0)).add
        (affine_polynomiallyBounded 40 24) |>.add (PolynomiallyBounded.const 1)
  convert h using 1
  funext width
  simp only [addBudget, budget, BinaryProductWriteback.budget, Nat.add_zero]
  ring

theorem doubleBudget_le (width : Nat) : doubleBudget width ≤ 81100 * (width + 1) ^ 3 := by
  have hRaw := rawTraceBudget_bound (fun _ => 18 * width + 15) (2 * width + 1)
  simp only [doubleBudget, budget, BinaryProductWriteback.budget]
  nlinarith [Nat.zero_le (width ^ 2), Nat.zero_le (width ^ 3)]

theorem addBudget_le (width : Nat) : addBudget width ≤ 216100 * (width + 1) ^ 3 := by
  have hRaw := rawTraceBudget_bound (fun _ => 24 * width + 10) (3 * width)
  simp only [addBudget, budget, BinaryProductWriteback.budget]
  nlinarith [Nat.zero_le (width ^ 2), Nat.zero_le (width ^ 3)]

private theorem pairs_length (pairs : List (Bool × Bool)) :
    (BinaryComparison.interleave pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [BinaryComparison.interleave, ih]; omega

private theorem triples_length (columns : List BinaryModularAddition.Column) :
    (BinaryModularAddition.interleave columns).length = 3 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [BinaryModularAddition.interleave, ih]; omega

/-- All complete matrices terminate, including modulus zero and residues
outside the domain of modular correctness. The native result has exactly
one bit per column, so subsequent phases retain the same matrix shape. -/
theorem double_runs (columns : List Column) (saved : List (Option Bool)) :
    ∃ (result : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      result.length = columns.length ∧ used ≤ doubleBudget columns.length ∧
      RunsFor doubleProgram (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } := by
  obtain ⟨result, hLength, correct⟩ := BinaryDoubleReduction.complete_output false
    (columns.map fun column => (column.accumulator, column.modulus))
  have correct' : evalWithin BinaryDoubleReduction.program (doubleRequest columns)
      (18 * columns.length + 15) = PMF.pure (some result) := by
    simpa [doubleRequest] using correct
  have halted := haltsWithin_of_no_timeout_support BinaryDoubleReduction.program (doubleRequest columns)
    (18 * columns.length + 15) (by rw [correct']; simp)
  obtain ⟨target, used, retained, hBound, hRun, hHalt, hInput, hOutput⟩ := runs
    BinaryProductGather.doubleInputProgram BinaryDoubleReduction.program columns
    (doubleRequest columns) result saved (30 * columns.length + 5) (fun _ => 18 * columns.length + 15)
    (by simpa using hLength) BinaryDoubleReduction.no_randomBit halted (by simpa [doubleRequest] using correct)
    (by simpa [BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
      show BinaryProductGather.doubleInputProgram.length = 50 from rfl, doubleRequest] using
      BinaryProductGather.eval_doubleInput_context columns [none] (none :: saved))
  refine ⟨result, target, used, retained, by simpa using hLength, ?_, hRun, hHalt, hInput, hOutput⟩
  have hRequest : (doubleRequest columns).length = 2 * columns.length + 1 := by
    simp [doubleRequest, pairs_length]
  simpa only [doubleBudget, hRequest] using hBound

theorem add_runs (selected : Bool) (columns : List Column) (saved : List (Option Bool)) :
    ∃ (result : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      result.length = columns.length ∧ used ≤ addBudget columns.length ∧
      RunsFor (addProgram selected) (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } ∧
      evalWithin BinaryModularAddition.program (addRequest selected columns) (24 * columns.length + 10) =
        PMF.pure (some result) := by
  obtain ⟨result, hLength, correct⟩ := BinaryModularAddition.complete_output
    (columns.map fun column => ((column.accumulator, if selected then column.operand else false), column.modulus))
  have correct' : evalWithin BinaryModularAddition.program (addRequest selected columns)
      (24 * columns.length + 10) = PMF.pure (some result) := by
    simpa [addRequest] using correct
  have halted := haltsWithin_of_no_timeout_support BinaryModularAddition.program (addRequest selected columns)
    (24 * columns.length + 10) (by rw [correct']; simp)
  obtain ⟨target, used, retained, hBound, hRun, hHalt, hInput, hOutput⟩ := runs
    (BinaryProductGather.addTriplesProgram selected) BinaryModularAddition.program columns
    (addRequest selected columns) result saved (30 * columns.length + 2) (fun _ => 24 * columns.length + 10)
    (by simpa using hLength) BinaryModularAddition.no_randomBit halted (by simpa [addRequest] using correct)
    (by simpa [BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
      show (BinaryProductGather.addTriplesProgram selected).length = 46 from rfl, addRequest] using
      BinaryProductGather.eval_addTriples_context selected columns [none] (none :: saved))
  refine ⟨result, target, used, retained, by simpa using hLength, ?_, hRun, hHalt, hInput, hOutput, correct'⟩
  have hRequest : (addRequest selected columns).length = 3 * columns.length := by
    simp [addRequest, triples_length]
  simpa only [addBudget, hRequest] using hBound


theorem double_runs_from_split (columns : List Column) (leading remaining : List Bool)
    (saved : List (Option Bool)) (hMatrix : leading ++ remaining = matrix columns) :
    ∃ (result : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      result.length = columns.length ∧ used ≤ doubleBudget columns.length ∧
      RunsFor doubleProgram
        { inputTape := { Tape.ofBits remaining with left := leading.reverse.map some },
          outputTape := { left := saved } } target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } ∧
      evalWithin BinaryDoubleReduction.program (doubleRequest columns) (18 * columns.length + 15) =
        PMF.pure (some result) := by
  obtain ⟨result, hLength, correct⟩ := BinaryDoubleReduction.complete_output false
    (columns.map fun column => (column.accumulator, column.modulus))
  have correct' : evalWithin BinaryDoubleReduction.program (doubleRequest columns)
      (18 * columns.length + 15) = PMF.pure (some result) := by
    simpa [doubleRequest] using correct
  have halted := haltsWithin_of_no_timeout_support BinaryDoubleReduction.program (doubleRequest columns)
    (18 * columns.length + 15) (by rw [correct']; simp)
  obtain ⟨target, used, retained, hBound, hRun, hHalt, hInput, hOutput⟩ := runs_from_split
    BinaryProductGather.doubleInputProgram BinaryDoubleReduction.program columns leading remaining
    (doubleRequest columns) result saved (30 * columns.length + 5) (fun _ => 18 * columns.length + 15)
    hMatrix (by simpa using hLength) BinaryDoubleReduction.no_randomBit halted (by simpa [doubleRequest] using correct)
    (by simpa [BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
      show BinaryProductGather.doubleInputProgram.length = 50 from rfl, doubleRequest] using
      BinaryProductGather.eval_doubleInput_context columns [none] (none :: saved))
  refine ⟨result, target, used, retained, by simpa using hLength, ?_, hRun, hHalt, hInput, hOutput, correct'⟩
  have hRequest : (doubleRequest columns).length = 2 * columns.length + 1 := by
    simp [doubleRequest, pairs_length]
  simpa only [doubleBudget, hRequest] using hBound

theorem add_runs_from_split (selected : Bool) (columns : List Column) (leading remaining : List Bool)
    (saved : List (Option Bool)) (hMatrix : leading ++ remaining = matrix columns) :
    ∃ (result : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      result.length = columns.length ∧ used ≤ addBudget columns.length ∧
      RunsFor (addProgram selected)
        { inputTape := { Tape.ofBits remaining with left := leading.reverse.map some },
          outputTape := { left := saved } } target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := result.reverse.map some ++ none :: retained } ∧
      evalWithin BinaryModularAddition.program (addRequest selected columns) (24 * columns.length + 10) =
        PMF.pure (some result) := by
  obtain ⟨result, hLength, correct⟩ := BinaryModularAddition.complete_output
    (columns.map fun column => ((column.accumulator, if selected then column.operand else false), column.modulus))
  have correct' : evalWithin BinaryModularAddition.program (addRequest selected columns)
      (24 * columns.length + 10) = PMF.pure (some result) := by
    simpa [addRequest] using correct
  have halted := haltsWithin_of_no_timeout_support BinaryModularAddition.program (addRequest selected columns)
    (24 * columns.length + 10) (by rw [correct']; simp)
  obtain ⟨target, used, retained, hBound, hRun, hHalt, hInput, hOutput⟩ := runs_from_split
    (BinaryProductGather.addTriplesProgram selected) BinaryModularAddition.program columns leading remaining
    (addRequest selected columns) result saved (30 * columns.length + 2) (fun _ => 24 * columns.length + 10)
    hMatrix (by simpa using hLength) BinaryModularAddition.no_randomBit halted (by simpa [addRequest] using correct)
    (by simpa [BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
      show (BinaryProductGather.addTriplesProgram selected).length = 46 from rfl, addRequest] using
      BinaryProductGather.eval_addTriples_context selected columns [none] (none :: saved))
  refine ⟨result, target, used, retained, by simpa using hLength, ?_, hRun, hHalt, hInput, hOutput, correct'⟩
  have hRequest : (addRequest selected columns).length = 3 * columns.length := by
    simp [addRequest, triples_length]
  simpa only [addBudget, hRequest] using hBound

end Machine.BinaryProductPhase
