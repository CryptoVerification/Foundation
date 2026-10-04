import Foundation.Machine.BinaryProductLoop
import Foundation.Machine.GuardedOutput
import Foundation.Machine.BitstringErasure

namespace Machine.BinaryProductFinalization

open BinaryProductSelection GuardedCompiler

/-- Extract the accumulator and physically erase the five-track matrix.
The result is copied back onto the matrix tape. The other tape may retain
arbitrary guarded arithmetic scratch, which is never part of the result.
All movement, erasure and copying are native one-cell instructions. -/
def program : Program :=
  [.moveRight .input, .moveRight .output] ++
    BinaryProductGather.resultProgram.asSubroutine 2 49 ++
    eraseOutputBlock.swapTapes.asSubroutine 49 55 ++ [.moveRight .input] ++
    rewindBitstring.swapTapes.asSubroutine 56 61 ++
    copyBitstring.swapTapes.asSubroutine 61 70 ++ [.halt]

def start (columns : List Column) (saved : List (Option Bool)) : Configuration :=
  { inputTape := { right := (matrix columns).map some ++ [none] },
    outputTape := { left := saved } }

def budget (width : Nat) : Nat := 58 * width + 15

private theorem call (pre source suffix : Program) (returnPc : Nat)
    (layout : program = Program.withSubroutine pre source suffix returnPc)
    (canonical returned actual : Configuration) (limit : Nat)
    (hPc : canonical.pc ≤ source.length) (hActive : canonical.halted = false)
    (hHalted : returned.halted = true)
    (hEval : evalConfigWithin source canonical limit = PMF.pure returned)
    (hLayout : (canonical.rebasePc pre.length).Equivalent actual) :
    ∃ (target : Configuration) (used : Nat), used ≤ limit ∧
      RunsFor program actual target used ∧ (returned.resumeAt returnPc).Equivalent target := by
  obtain ⟨target, used, hUsed, native, hTarget⟩ := nativeCall_of_eval
    pre source suffix returnPc canonical returned actual limit hPc hActive hHalted hEval hLayout
  rw [← layout] at native
  exact ⟨target, used, hUsed, native, hTarget⟩

private theorem cells_append_blank (bits : List Bool) (index : Nat) :
    (bits.map some ++ [none]).getD index none = (bits.map some).getD index none := by
  induction bits generalizing index with
  | nil => cases index <;> simp
  | cons bit rest ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [List.map_cons, List.cons_append, List.getD_cons_succ] using ih index

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

theorem runs_with_layout (columns : List Column) (saved : List (Option Bool)) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget columns.length ∧
      RunsFor program (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.bits = columns.map Column.accumulator ∧
      target.inputTape.Equivalent
        { left := (columns.map Column.accumulator).reverse.map some ++ [none],
          right := List.replicate ((matrix columns).length - columns.length) none } := by
  let mat := matrix columns
  let bits := columns.map Column.accumulator
  let movedInput : Configuration :=
    { start columns saved with pc := 1, inputTape := (start columns saved).inputTape.moveRight }
  let moved : Configuration :=
    { movedInput with pc := 2, outputTape := movedInput.outputTape.moveRight }
  have first : Step program (start columns saved) movedInput := by
    simp [Step, successors, next, program, start, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have second : Step program movedInput moved := by
    simp [Step, successors, next, program, start, movedInput, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  let pre1 : Program := [.moveRight .input, .moveRight .output]
  let suffix1 := eraseOutputBlock.swapTapes.asSubroutine 49 55 ++ [.moveRight .input] ++
    rewindBitstring.swapTapes.asSubroutine 56 61 ++ copyBitstring.swapTapes.asSubroutine 61 70 ++ [.halt]
  have layout1 : program = Program.withSubroutine pre1 BinaryProductGather.resultProgram suffix1 49 := by
    simp [program, Program.withSubroutine, pre1, suffix1, List.append_assoc]
  let gathered : Configuration :=
    { pc := 45, inputTape := { left := mat.reverse.map some ++ [none] },
      outputTape := { left := bits.reverse.map some ++ none :: saved }, halted := true }
  have gatherLayout : ((BinaryProductGather.gatherStart [none] (none :: saved) mat).rebasePc 2).Equivalent moved := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    change ({ Tape.ofBits mat with left := [none] } : Tape).Equivalent
      (({ right := mat.map some ++ [none] } : Tape).moveRight)
    cases hMat : mat with
    | nil =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro index
        simpa [Tape.ofBits, Tape.moveRight] using
          (Tape.blank_padding_equivalent [none] 1).2.2 index |>.symm
    | cons bit rest =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro index
        simpa [Tape.ofBits, Tape.moveRight] using
          (cells_append_blank rest index).symm
  obtain ⟨s1, u1, hu1, r1, e1⟩ := call pre1 BinaryProductGather.resultProgram suffix1 49 layout1
    (BinaryProductGather.gatherStart [none] (none :: saved) mat) gathered moved
    (30 * columns.length + 2) (by change 0 ≤ _; omega) rfl rfl
    (by simpa [gathered, mat, bits, BinaryProductGather.gatherFinish] using
      BinaryProductGather.eval_result_context columns [none] (none :: saved)) gatherLayout
  let output : Tape := { left := bits.reverse.map some ++ none :: saved }
  let pre2 := pre1 ++ BinaryProductGather.resultProgram.asSubroutine 2 49
  let suffix2 := [.moveRight .input] ++ rewindBitstring.swapTapes.asSubroutine 56 61 ++
    copyBitstring.swapTapes.asSubroutine 61 70 ++ [.halt]
  have layout2 : program = Program.withSubroutine pre2 eraseOutputBlock.swapTapes suffix2 55 := by
    simp [program, Program.withSubroutine, pre2, pre1, suffix2, List.append_assoc,
      show BinaryProductGather.resultProgram.length = 46 from rfl]
  have eraseEval := (eraseOutputBlock_runs output [] mat []).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit
      (Program.swapTapes_no_randomBit _ eraseOutputBlock_no_randomBit)
  obtain ⟨s2, u2, hu2, r2, e2⟩ := call pre2 eraseOutputBlock.swapTapes suffix2 55 layout2
    (eraseOutputBlockStart output [] mat []).swapTapes
    (eraseOutputBlockFinish output [] mat []).swapTapes s1
    (4 * mat.length + 3) (by change 0 ≤ _; omega) rfl rfl eraseEval (by
      change ({
        pc := 49
        inputTape := { left := mat.reverse.map some ++ [none] }
        outputTape := output } : Configuration).Equivalent s1
      exact e1)
  let restored : Configuration := { s2 with pc := 56, inputTape := s2.inputTape.moveRight }
  have restoreStep : Step program s2 restored := by
    have hp : s2.pc = 55 := e2.1.symm
    have ha : s2.halted = false := e2.2.1.symm
    have lookup : program[55]? = some (.moveRight .input) := by decide
    simp [Step, successors, next, hp, ha, lookup, restored, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  let clean : Tape := { left := [none], right := List.replicate mat.length none }
  let pre3 := pre2 ++ eraseOutputBlock.swapTapes.asSubroutine 49 55 ++ [.moveRight .input]
  let suffix3 := copyBitstring.swapTapes.asSubroutine 61 70 ++ [.halt]
  have layout3 : program = Program.withSubroutine pre3 rewindBitstring.swapTapes suffix3 61 := by
    simp [program, Program.withSubroutine, pre3, pre2, pre1, suffix3, List.append_assoc,
      show BinaryProductGather.resultProgram.length = 46 from rfl,
      show eraseOutputBlock.length = 5 from rfl]
  have rewindEval := (rewindScratch_runs saved bits clean).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit
      (Program.swapTapes_no_randomBit _ rewindBitstring_no_randomBit)
  have rewindLayout : ((rewindScratchStart saved bits clean).swapTapes.rebasePc pre3.length).Equivalent restored := by
    refine ⟨by change 56 = _; rfl, e2.2.1, ?_, e2.2.2.2⟩
    have same := e2.2.2.1.moveRight
    change ({ right := List.replicate (mat.reverse.length + 1) none ++ [] } : Tape).moveRight.Equivalent
      s2.inputTape.moveRight at same
    have right : List.replicate (mat.length + 1) (none : Option Bool) =
        none :: List.replicate mat.length none := rfl
    rw [List.length_reverse, List.append_nil, right] at same
    exact same
  obtain ⟨s3, u3, hu3, r3, e3⟩ := call pre3 rewindBitstring.swapTapes suffix3 61 layout3
    (rewindScratchStart saved bits clean).swapTapes
    (rewindScratchFinish saved bits clean).swapTapes restored
    (2 * bits.length + 4) (by change 0 ≤ _; omega) rfl rfl rewindEval rewindLayout
  let pre4 := pre3 ++ rewindBitstring.swapTapes.asSubroutine 56 61
  have layout4 : program = Program.withSubroutine pre4 copyBitstring.swapTapes [.halt] 70 := by
    simp [program, Program.withSubroutine, pre4, pre3, pre2, pre1, List.append_assoc,
      show BinaryProductGather.resultProgram.length = 46 from rfl,
      show eraseOutputBlock.length = 5 from rfl, show rewindBitstring.length = 4 from rfl]
  have copyLayout : ((copyScratchStart (none :: saved) [none] bits mat.length).swapTapes.rebasePc
      pre4.length).Equivalent s3 := by
    have expected : ((copyScratchStart (none :: saved) [none] bits mat.length).swapTapes.rebasePc
        pre4.length) = ((rewindScratchFinish saved bits clean).swapTapes.resumeAt 61) := by
      change ({
        pc := 61
        inputTape := clean
        outputTape := { packedLogicalInput bits with left := none :: saved } } : Configuration) = _
      cases bits <;> simp [rewindScratchFinish, packedLogicalInput, rewoundTape,
        clean, Configuration.swapTapes, Configuration.resumeAt, Tape.moveRight]
    rw [expected]
    exact e3
  have copyEval := (copyScratch_runs (none :: saved) [none] bits mat.length).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit
      (Program.swapTapes_no_randomBit _ copyBitstring_no_randomBit)
  obtain ⟨s4, u4, hu4, r4, e4⟩ := call pre4 copyBitstring.swapTapes [.halt] 70 layout4
    (copyScratchStart (none :: saved) [none] bits mat.length).swapTapes
    (copyScratchFinish (none :: saved) [none] bits mat.length).swapTapes s3
    (copyBitstringSteps bits) (by change 0 ≤ _; omega) rfl rfl copyEval copyLayout
  have last : Step program s4 { s4 with halted := true } := by
    have hp : s4.pc = 70 := e4.1.symm
    have ha : s4.halted = false := e4.2.1.symm
    have lookup : program[70]? = some .halt := by decide
    simp [Step, successors, next, hp, ha, lookup, Instruction.next]
  have native := ((((RunsFor.succ (RunsFor.succ (RunsFor.zero _) first) second).trans r1).trans r2).succ
    restoreStep).trans r3 |>.trans r4 |>.succ last
  refine ⟨{ s4 with halted := true }, 2 + u1 + u2 + 1 + u3 + u4 + 1, ?_, native, rfl, ?_, ?_⟩
  · have hMat : mat.length = 5 * columns.length := by
      simp [mat, matrix, row, List.length_flatMap, Nat.mul_comm]
    have hBits : bits.length = columns.length := List.length_map _
    have hCopy := copyBitstringSteps_le bits
    dsimp only [budget]
    omega
  · have hBits := e4.2.2.1.bits.symm
    change s4.inputTape.bits = ({
      left := bits.reverse.map some ++ [none]
      right := List.replicate (mat.length - bits.length) none } : Tape).bits at hBits
    simpa [Tape.bits, bits] using hBits


  · simpa only [bits, mat, Configuration.inputTape, Configuration.resumeAt,
      Configuration.swapTapes, copyScratchFinish, List.length_map] using e4.2.2.1.symm

/-- The original output-only projection remains available. -/
theorem runs (columns : List Column) (saved : List (Option Bool)) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget columns.length ∧
      RunsFor program (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.bits = columns.map Column.accumulator := by
  obtain ⟨target, used, hUsed, run, hHalt, hBits, _⟩ := runs_with_layout columns saved
  exact ⟨target, used, hUsed, run, hHalt, hBits⟩

end Machine.BinaryProductFinalization
