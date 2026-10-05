import Foundation.Crypto.Semantics.Machine.NativeInvocation
import Foundation.Crypto.Semantics.Machine.BinaryProductSelection
import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine.BinaryPowerSeed

open BinaryProductSelection

/-- Initialize the power accumulator to one by a charged write to the
first matrix cell, then traverse the same physical matrix back to its end. -/
def program : Program := Program.withSubroutine [] rewindBitstring
  [.branch .input 10 6 6, .write .input true,
   .branch .input 10 8 8, .moveRight .input, .jump 7, .halt] 5

def seeded : List Column → List Column
  | [] => []
  | column :: rest => { column with accumulator := true } :: rest

private def seedBits : List Bool → List Bool
  | [] => []
  | _ :: rest => true :: rest

private theorem seedBits_matrix (columns : List Column) : seedBits (matrix columns) = matrix (seeded columns) := by
  cases columns <;> rfl

private def scanState (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 7, inputTape := { Tape.ofBits bits with left := before }, outputTape := output }

private def finish (before : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 10, inputTape := { left := before }, outputTape := output, halted := true }

private theorem scan_eval (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    evalConfigWithin program (scanState before bits output) (3 * bits.length + 2) =
      PMF.pure (finish (bits.reverse.map some ++ before) output) := by
  induction bits generalizing before with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, program, Program.withSubroutine,
        rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
        scanState, finish, Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]
  | cons bit rest ih =>
      have time : 3 * (bit :: rest).length + 2 = 3 + (3 * rest.length + 2) := by simp; omega
      rw [time, evalConfigWithin_add]
      have first : evalConfigWithin program (scanState before (bit :: rest) output) 3 =
          PMF.pure (scanState (some bit :: before) rest output) := by
        cases bit <;> cases rest <;>
          simp [evalConfigWithin, stepPMF, next, program, Program.withSubroutine,
            rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
            scanState, Instruction.next, Configuration.tape, Configuration.advance,
            Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]
      rw [first, PMF.pure_bind]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using ih (some bit :: before)

private theorem tail_eval (bits : List Bool) (output : Tape) :
    evalConfigWithin program { pc := 5, inputTape := Tape.ofBits bits, outputTape := output }
      (3 * bits.length + 4) = PMF.pure (finish ((seedBits bits).reverse.map some) output) := by
  cases bits with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, program, Program.withSubroutine,
        rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
        seedBits, finish, Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]
  | cons bit rest =>
      have time : 3 * (bit :: rest).length + 4 = 2 + (3 * (true :: rest).length + 2) := by simp; omega
      rw [time, evalConfigWithin_add]
      have first : evalConfigWithin program { pc := 5, inputTape := Tape.ofBits (bit :: rest), outputTape := output } 2 =
          PMF.pure (scanState [] (true :: rest) output) := by
        cases bit <;>
          simp [evalConfigWithin, stepPMF, next, program, Program.withSubroutine,
            rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
            scanState, Instruction.next, Configuration.tape, Configuration.advance,
            Configuration.updateTape, Tape.ofBits, Tape.write, PMF.pure_bind]
      rw [first, PMF.pure_bind, scan_eval]
      simp only [List.append_nil, seedBits]

def start (columns : List Column) (saved : List (Option Bool)) : Configuration :=
  { inputTape := { left := (matrix columns).reverse.map some }, outputTape := { left := saved } }

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

theorem runs (columns : List Column) (saved : List (Option Bool)) :
    ∃ (target : Configuration) (used : Nat), used ≤ 25 * columns.length + 8 ∧
      RunsFor program (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (seeded columns)).reverse.map some } ∧
      target.outputTape.Equivalent { left := saved } := by
  let bits := matrix columns
  let output : Tape := { left := saved }
  let returned := rewindBitstringFinish bits output
  obtain ⟨middle, firstTime, hFirst, native, layout⟩ := nativeCall_of_eval [] rewindBitstring
    [.branch .input 10 6 6, .write .input true,
     .branch .input 10 8 8, .moveRight .input, .jump 7, .halt] 5
    (rewindBitstringStart bits output) returned (start columns saved) (2 * bits.length + 4)
    (by change 0 ≤ _; omega) rfl rfl (rewindBitstring_eval bits output) (Configuration.Equivalent.refl _)
  let canonical : Configuration := { pc := 5, inputTape := Tape.ofBits bits, outputTape := output }
  have middleLayout : canonical.Equivalent middle :=
    ⟨layout.1, layout.2.1, (rewindBitstringFinish_input_equivalent bits output).symm.trans layout.2.2.1, layout.2.2.2⟩
  have hEval := tail_eval bits output
  have tailRun := (mem_support_evalConfigWithin_iff program canonical (finish ((seedBits bits).reverse.map some) output)
    (3 * bits.length + 4)).mp (by rw [hEval]; simp)
  obtain ⟨tailTime, hTail, trace⟩ := tailRun.toRunsFor_le
  obtain ⟨target, actualTail, targetLayout⟩ := trace.exists_equivalent middleLayout
  refine ⟨target, firstTime + tailTime, ?_, native.trans actualTail, targetLayout.2.1.symm, ?_, ?_⟩
  · have width : bits.length = 5 * columns.length := by simp [bits, matrix, row]; omega
    omega
  · simpa only [finish, seedBits_matrix, bits] using targetLayout.2.2.1.symm
  · exact targetLayout.2.2.2.symm

@[simp] theorem seeded_length (columns : List Column) : (seeded columns).length = columns.length := by
  cases columns <;> rfl

end Machine.BinaryPowerSeed
