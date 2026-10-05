import Foundation.Crypto.Semantics.Machine.GuardedTape

namespace Machine.GuardedCompiler

open VirtualCell

/-- Copy contiguous raw input bits into a guarded output region. The header
is `01`, every input bit `b` is written as `1b`, and a final logical blank is
written as `00`. Each write and movement is an original one-cell opcode.
The output head ends at that final blank pair, not at the first input pair.
This is one operational input-preparation component, not the complete
two-tape initialization of an embedded source program. -/
def packInput : Program :=
  [.write .output false, .moveRight .output,
   .write .output true, .moveRight .output,
   .branch .input 17 5 11,
   .write .output true, .moveRight .output, .write .output false,
   .moveRight .output, .moveRight .input, .jump 4,
   .write .output true, .moveRight .output, .write .output true,
   .moveRight .output, .moveRight .input, .jump 4,
   .write .output false, .moveRight .output, .write .output false,
   .moveLeft .output, .halt]

/-- Caller prefixes already behind each head are retained. The current raw
input is contiguous and the output region from its current head is blank. -/
def packInputStart (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    Configuration :=
  { inputTape := { Tape.ofBits input with left := beforeInput },
    outputTape := { left := beforeOutput } }

private def packingState (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) : Configuration :=
  { pc := 4,
    inputTape := { Tape.ofBits remaining with left := copied.reverse.map some ++ beforeInput },
    outputTape := { left := (encodedLeftCells (copied.reverse.map some) ++
      some true :: some false :: beforeOutput) } }

/-- The packed output represents the source tape after its input has been
scanned to the first blank. The raw input bits remain on the input tape.
Both saved caller prefixes survive, and head positions are explicit. -/
def packInputFinish (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    Configuration :=
  { pc := 21,
    inputTape := { left := input.reverse.map some ++ beforeInput },
    outputTape := encodeTape beforeOutput { left := input.reverse.map some },
    halted := true }

private theorem pack_header (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    RunsFor packInput (packInputStart beforeInput beforeOutput input)
      (packingState beforeInput beforeOutput [] input) 4 := by
  let initial := packInputStart beforeInput beforeOutput input
  let first := (initial.updateTape .output (fun t => t.write (some false))).advance
  let second := (first.updateTape .output Tape.moveRight).advance
  let third := (second.updateTape .output (fun t => t.write (some true))).advance
  have h0 : Step packInput initial first := by
    simp [Step, successors, next, packInput, initial, first, packInputStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step packInput first second := by
    simp [Step, successors, next, packInput, initial, first, second, packInputStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step packInput second third := by
    simp [Step, successors, next, packInput, initial, first, second, third, packInputStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step packInput third (packingState beforeInput beforeOutput [] input) := by
    simp [Step, successors, next, packInput, initial, first, second, third, packInputStart,
      packingState, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.write, encodedLeftCells]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3

private theorem pack_one_bit (beforeInput beforeOutput : List (Option Bool))
    (copied rest : List Bool) (bit : Bool) :
    RunsFor packInput (packingState beforeInput beforeOutput copied (bit :: rest))
      (packingState beforeInput beforeOutput (copied ++ [bit]) rest) 7 := by
  let initial := packingState beforeInput beforeOutput copied (bit :: rest)
  let selected : Configuration := { initial with pc := if bit then 11 else 5 }
  let tagged := (selected.updateTape .output (fun t => t.write (some true))).advance
  let atBit := (tagged.updateTape .output Tape.moveRight).advance
  let written := (atBit.updateTape .output (fun t => t.write (some bit))).advance
  let movedOutput := (written.updateTape .output Tape.moveRight).advance
  let movedInput := (movedOutput.updateTape .input Tape.moveRight).advance
  have h0 : Step packInput initial selected := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, packingState,
      Tape.ofBits, Instruction.next, Configuration.tape]
  have h1 : Step packInput selected tagged := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, tagged, packingState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step packInput tagged atBit := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, tagged, atBit,
      packingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step packInput atBit written := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, tagged, atBit,
      written, packingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step packInput written movedOutput := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, tagged, atBit,
      written, movedOutput, packingState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step packInput movedOutput movedInput := by
    cases bit <;> simp [Step, successors, next, packInput, initial, selected, tagged, atBit,
      written, movedOutput, movedInput, packingState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step packInput movedInput
      (packingState beforeInput beforeOutput (copied ++ [bit]) rest) := by
    cases bit <;> cases rest <;>
      simp [Step, successors, next, packInput, initial, selected, tagged, atBit,
        written, movedOutput, movedInput, packingState, Instruction.next,
        Configuration.updateTape, Configuration.advance, Tape.ofBits, Tape.moveRight,
        Tape.write, List.reverse_append, encodedLeftCells, code]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6

private theorem pack_blank (beforeInput beforeOutput : List (Option Bool)) (copied : List Bool) :
    RunsFor packInput (packingState beforeInput beforeOutput copied [])
      (packInputFinish beforeInput beforeOutput copied) 6 := by
  let initial := packingState beforeInput beforeOutput copied []
  let selected : Configuration := { initial with pc := 17 }
  let first := (selected.updateTape .output (fun t => t.write (some false))).advance
  let second := (first.updateTape .output Tape.moveRight).advance
  let third := (second.updateTape .output (fun t => t.write (some false))).advance
  let restored := (third.updateTape .output Tape.moveLeft).advance
  have h0 : Step packInput initial selected := by
    simp [Step, successors, next, packInput, initial, selected, packingState,
      Tape.ofBits, Instruction.next, Configuration.tape]
  have h1 : Step packInput selected first := by
    simp [Step, successors, next, packInput, initial, selected, first, packingState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step packInput first second := by
    simp [Step, successors, next, packInput, initial, selected, first, second, packingState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step packInput second third := by
    simp [Step, successors, next, packInput, initial, selected, first, second, third,
      packingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step packInput third restored := by
    simp [Step, successors, next, packInput, initial, selected, first, second, third,
      restored, packingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step packInput restored (packInputFinish beforeInput beforeOutput copied) := by
    simp [Step, successors, next, packInput, initial, selected, first, second, third,
      restored, packingState, packInputFinish, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.ofBits, Tape.moveRight, Tape.moveLeft, Tape.write,
      encodeTape, pairTape, code, encodedCells]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5

private theorem pack_loop (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) :
    RunsFor packInput (packingState beforeInput beforeOutput copied remaining)
      (packInputFinish beforeInput beforeOutput (copied ++ remaining))
      (7 * remaining.length + 6) := by
  induction remaining generalizing copied with
  | nil => simpa using pack_blank beforeInput beforeOutput copied
  | cons bit rest ih =>
      have run := (pack_one_bit beforeInput beforeOutput copied rest bit).trans
        (ih (copied ++ [bit]))
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using run

/-- Four header transitions, seven for each copied bit, and six to append
the logical blank and halt. Neither encoding nor head positioning is free. -/
theorem packInput_runs (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    RunsFor packInput (packInputStart beforeInput beforeOutput input)
      (packInputFinish beforeInput beforeOutput input) (7 * input.length + 10) := by
  have run := (pack_header beforeInput beforeOutput input).trans
    (pack_loop beforeInput beforeOutput [] input)
  simp only [List.nil_append] at run
  convert run using 1; omega

theorem packInput_no_randomBit (which : TapeId) :
    Instruction.randomBit which ∉ packInput := by simp [packInput]

theorem packInput_control_closed (c d : Configuration) (hPc : c.pc < packInput.length)
    (step : Step packInput c d) (_hRunning : d.halted = false) : d.pc < packInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 22 at hPc
  interval_cases hIndex : c.pc <;>
    cases hCell : c.inputTape.current with
    | none =>
        simp [Step, successors, next, hActive, hIndex, packInput,
          Instruction.next, hCell, Configuration.tape] at step
        subst d
        simp [packInput, Configuration.advance, Configuration.updateTape, hIndex]
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, hActive, hIndex, packInput,
            Instruction.next, hCell, Configuration.tape] at step <;>
          subst d <;>
          simp [packInput, Configuration.advance, Configuration.updateTape, hIndex]

theorem packInput_eval (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin packInput (packInputStart beforeInput beforeOutput input)
      (7 * input.length + 10) = PMF.pure (packInputFinish beforeInput beforeOutput input) :=
  (packInput_runs beforeInput beforeOutput input).evalConfigWithin_eq_pure_of_no_randomBit
    packInput_no_randomBit

/-- This input-preparation component also executes as real embedded code.
It returns with both tape postconditions and its exact transition count.
Random instructions in the surrounding caller need not be excluded. -/
theorem packInput_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin (Program.withSubroutine pre packInput suffix returnPc)
      ((packInputStart beforeInput beforeOutput input).rebasePc pre.length)
      (7 * input.length + 10) =
      PMF.pure ((packInputFinish beforeInput beforeOutput input).resumeAt returnPc) :=
  (packInput_runs beforeInput beforeOutput input).evalConfigWithin_withSubroutine_halted_of_closed
    pre packInput suffix returnPc (by simp [packInputStart, packInput]) rfl rfl
    packInput_control_closed packInput_no_randomBit

theorem packInput_all_branches_halted (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) (final : Configuration)
    (run : PaddedRunsFor packInput (packInputStart beforeInput beforeOutput input)
      final (7 * input.length + 10)) : final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [packInput_eval] at hMem
  have hFinal : final = packInputFinish beforeInput beforeOutput input := by simpa using hMem
  subst final
  rfl

theorem packInput_haltsWithin (input : List Bool) :
    HaltsWithin packInput input (7 * input.length + 10) := by
  intro final run
  have hInitial : packInputStart [] [] input = Configuration.initial input := by
    cases input <;> rfl
  rw [← hInitial] at run
  exact packInput_all_branches_halted [] [] input final run

theorem packInput_polynomialTime : PolynomialTime packInput := by
  refine ⟨fun m => 7 * m + 10, ?_, packInput_haltsWithin⟩
  exact ((PolynomiallyBounded.const 7).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 10)

end Machine.GuardedCompiler
