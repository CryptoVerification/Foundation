import Foundation.Machine.GuardedRewind
import Foundation.Machine.TapeEquivalence

namespace Machine.GuardedCompiler

open VirtualCell

/-- Transfer the packed input from output to a fresh guarded input region.
Every copied bit uses ordinary one-cell instructions, and its old output
pair is overwritten by `00`. The original input prefix remains behind the
new guard. Both heads end at the final logical blank, so subsequent rewind
operations are still necessary before entering the embedded program. -/
def transferPackedInput : Program :=
  [.write .input false, .moveRight .input,
   .write .input true, .moveRight .input,
   .branch .output 27 22 5,
   .write .output false, .moveRight .output, .branch .output 27 8 15,
   .write .input true, .moveRight .input, .write .input false,
   .moveRight .input, .write .output false, .moveRight .output, .jump 4,
   .write .input true, .moveRight .input, .write .input true,
   .moveRight .input, .write .output false, .moveRight .output, .jump 4,
   .write .input false, .moveRight .input, .write .input false,
   .moveLeft .input, .halt, .halt]

theorem packedLogicalInput_nil : packedLogicalInput [] = ({} : Tape) := rfl

theorem packedLogicalInput_cons (bit : Bool) (rest : List Bool) :
    packedLogicalInput (bit :: rest) =
      { current := some bit, right := rest.map some ++ [none] } := by
  simp [packedLogicalInput, rewoundTape, List.reverse_cons]

/-- Entry contract: the output head points to the first packed data pair,
while the input head begins a blank region beyond an arbitrary saved prefix. -/
def transferPackedInputStart (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) : Configuration :=
  { inputTape := { left := beforeInput },
    outputTape := encodeTape beforeOutput (packedLogicalInput input) }

private def transferState (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) : Configuration :=
  { pc := 4,
    inputTape := { left := (encodedLeftCells (copied.reverse.map some) ++
      some true :: some false :: beforeInput) },
    outputTape := encodeTape beforeOutput
      { packedLogicalInput remaining with left := List.replicate copied.length none } }

/-- The transferred bits are in the input region. The output region now
contains only logical blanks; neither saved caller prefix has been erased. -/
def transferPackedInputFinish (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) : Configuration :=
  { pc := 26,
    inputTape := encodeTape beforeInput { left := input.reverse.map some },
    outputTape := encodeTape beforeOutput { left := List.replicate input.length none },
    halted := true }

private theorem transfer_header (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) :
    RunsFor transferPackedInput (transferPackedInputStart beforeInput beforeOutput input)
      (transferState beforeInput beforeOutput [] input) 4 := by
  let initial := transferPackedInputStart beforeInput beforeOutput input
  let first := (initial.updateTape .input (fun t => t.write (some false))).advance
  let second := (first.updateTape .input Tape.moveRight).advance
  let third := (second.updateTape .input (fun t => t.write (some true))).advance
  have h0 : Step transferPackedInput initial first := by
    simp [Step, successors, next, transferPackedInput, initial, first,
      transferPackedInputStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step transferPackedInput first second := by
    simp [Step, successors, next, transferPackedInput, initial, first, second,
      transferPackedInputStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step transferPackedInput second third := by
    simp [Step, successors, next, transferPackedInput, initial, first, second, third,
      transferPackedInputStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step transferPackedInput third (transferState beforeInput beforeOutput [] input) := by
    cases input <;> simp [Step, successors, next, transferPackedInput, initial, first, second, third,
      transferPackedInputStart, transferState, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.write, encodedLeftCells,
      packedLogicalInput_nil, packedLogicalInput_cons]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3

private theorem transfer_bit (beforeInput beforeOutput : List (Option Bool))
    (copied rest : List Bool) (bit : Bool) :
    RunsFor transferPackedInput (transferState beforeInput beforeOutput copied (bit :: rest))
      (transferState beforeInput beforeOutput (copied ++ [bit]) rest) 11 := by
  let initial := transferState beforeInput beforeOutput copied (bit :: rest)
  let selected : Configuration := { initial with pc := 5 }
  let cleared := (selected.updateTape .output (fun t => t.write (some false))).advance
  let atBit := (cleared.updateTape .output Tape.moveRight).advance
  let chosen : Configuration := { atBit with pc := if bit then 15 else 8 }
  let tagged := (chosen.updateTape .input (fun t => t.write (some true))).advance
  let atDestination := (tagged.updateTape .input Tape.moveRight).advance
  let written := (atDestination.updateTape .input (fun t => t.write (some bit))).advance
  let movedInput := (written.updateTape .input Tape.moveRight).advance
  let erased := (movedInput.updateTape .output (fun t => t.write (some false))).advance
  let movedOutput := (erased.updateTape .output Tape.moveRight).advance
  have h0 : Step transferPackedInput initial selected := by
    simp [Step, successors, next, transferPackedInput, initial, selected, transferState,
      packedLogicalInput_cons, encodeTape, pairTape, code, Instruction.next, Configuration.tape]
  have h1 : Step transferPackedInput selected cleared := by
    simp [Step, successors, next, transferPackedInput, initial, selected, cleared, transferState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step transferPackedInput cleared atBit := by
    simp [Step, successors, next, transferPackedInput, initial, selected, cleared, atBit,
      transferState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step transferPackedInput atBit chosen := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, transferState, packedLogicalInput_cons, encodeTape, pairTape, code,
      Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
      Tape.moveRight, Tape.write]
  have h4 : Step transferPackedInput chosen tagged := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, transferState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step transferPackedInput tagged atDestination := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, atDestination, transferState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step transferPackedInput atDestination written := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, atDestination, written, transferState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h7 : Step transferPackedInput written movedInput := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, atDestination, written, movedInput, transferState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h8 : Step transferPackedInput movedInput erased := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, atDestination, written, movedInput, erased, transferState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h9 : Step transferPackedInput erased movedOutput := by
    cases bit <;> simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
      atBit, chosen, tagged, atDestination, written, movedInput, erased, movedOutput,
      transferState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h10 : Step transferPackedInput movedOutput
      (transferState beforeInput beforeOutput (copied ++ [bit]) rest) := by
    cases bit <;> cases rest <;>
      simp [Step, successors, next, transferPackedInput, initial, selected, cleared,
        atBit, chosen, tagged, atDestination, written, movedInput, erased, movedOutput,
        transferState, packedLogicalInput_nil, packedLogicalInput_cons, encodeTape, pairTape,
        code, encodedCells, encodedLeftCells, Instruction.next, Configuration.updateTape,
        Configuration.advance, Tape.moveRight, Tape.write, List.reverse_append,
        List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10

private theorem transfer_blank (beforeInput beforeOutput : List (Option Bool))
    (copied : List Bool) :
    RunsFor transferPackedInput (transferState beforeInput beforeOutput copied [])
      (transferPackedInputFinish beforeInput beforeOutput copied) 6 := by
  let initial := transferState beforeInput beforeOutput copied []
  let selected : Configuration := { initial with pc := 22 }
  let first := (selected.updateTape .input (fun t => t.write (some false))).advance
  let second := (first.updateTape .input Tape.moveRight).advance
  let third := (second.updateTape .input (fun t => t.write (some false))).advance
  let restored := (third.updateTape .input Tape.moveLeft).advance
  have h0 : Step transferPackedInput initial selected := by
    simp [Step, successors, next, transferPackedInput, initial, selected, transferState,
      packedLogicalInput_nil, encodeTape, pairTape, code, Instruction.next, Configuration.tape]
  have h1 : Step transferPackedInput selected first := by
    simp [Step, successors, next, transferPackedInput, initial, selected, first, transferState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step transferPackedInput first second := by
    simp [Step, successors, next, transferPackedInput, initial, selected, first, second,
      transferState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step transferPackedInput second third := by
    simp [Step, successors, next, transferPackedInput, initial, selected, first, second, third,
      transferState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step transferPackedInput third restored := by
    simp [Step, successors, next, transferPackedInput, initial, selected, first, second, third,
      restored, transferState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step transferPackedInput restored
      (transferPackedInputFinish beforeInput beforeOutput copied) := by
    simp [Step, successors, next, transferPackedInput, initial, selected, first, second, third,
      restored, transferState, transferPackedInputFinish, packedLogicalInput_nil,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft, Tape.write, encodeTape, pairTape, code, encodedCells]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5

private theorem transfer_loop (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) :
    RunsFor transferPackedInput (transferState beforeInput beforeOutput copied remaining)
      (transferPackedInputFinish beforeInput beforeOutput (copied ++ remaining))
      (11 * remaining.length + 6) := by
  induction remaining generalizing copied with
  | nil => simpa using transfer_blank beforeInput beforeOutput copied
  | cons bit rest ih =>
      have run := (transfer_bit beforeInput beforeOutput copied rest bit).trans
        (ih (copied ++ [bit]))
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using run

/-- Four transitions write the new guard, eleven transfer and clear each
bit, and six materialize the destination blank and halt. -/
theorem transferPackedInput_runs (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) :
    RunsFor transferPackedInput (transferPackedInputStart beforeInput beforeOutput input)
      (transferPackedInputFinish beforeInput beforeOutput input) (11 * input.length + 10) := by
  have run := (transfer_header beforeInput beforeOutput input).trans
    (transfer_loop beforeInput beforeOutput [] input)
  simp only [List.nil_append] at run
  convert run using 1; omega

theorem transferPackedInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ transferPackedInput := by simp [transferPackedInput]

theorem transferPackedInput_control_closed (c d : Configuration)
    (hPc : c.pc < transferPackedInput.length) (step : Step transferPackedInput c d)
    (_hRunning : d.halted = false) : d.pc < transferPackedInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 28 at hPc
  interval_cases hIndex : c.pc <;>
    cases hCell : c.outputTape.current with
    | none =>
        simp [Step, successors, next, hActive, hIndex, transferPackedInput,
          Instruction.next, hCell, Configuration.tape] at step
        subst d
        simp [transferPackedInput, Configuration.advance, Configuration.updateTape, hIndex]
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, hActive, hIndex, transferPackedInput,
            Instruction.next, hCell, Configuration.tape] at step <;>
          subst d <;>
          simp [transferPackedInput, Configuration.advance, Configuration.updateTape, hIndex]

theorem transferPackedInput_eval (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) :
    evalConfigWithin transferPackedInput (transferPackedInputStart beforeInput beforeOutput input)
      (11 * input.length + 10) =
      PMF.pure (transferPackedInputFinish beforeInput beforeOutput input) :=
  (transferPackedInput_runs beforeInput beforeOutput input).evalConfigWithin_eq_pure_of_no_randomBit
    transferPackedInput_no_randomBit

/-- Transfer is an ordinary callable routine, including in a randomized
caller. Its contract records the exact tapes and exact return count. -/
theorem transferPackedInput_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin (Program.withSubroutine pre transferPackedInput suffix returnPc)
      ((transferPackedInputStart beforeInput beforeOutput input).rebasePc pre.length)
      (11 * input.length + 10) =
      PMF.pure ((transferPackedInputFinish beforeInput beforeOutput input).resumeAt returnPc) :=
  (transferPackedInput_runs beforeInput beforeOutput input).evalConfigWithin_withSubroutine_halted_of_closed
    pre transferPackedInput suffix returnPc
    (by simp [transferPackedInputStart, transferPackedInput]) rfl rfl
    transferPackedInput_control_closed transferPackedInput_no_randomBit

theorem rewindRegionSteps_blanks (count : Nat) :
    rewindRegionSteps (List.replicate count none) = 7 * count + 7 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, rewindRegionSteps, ih, Nat.mul_add]; omega

/-- Initialize both tapes for a guarded execution from contiguous raw
input. Packing, each return jump, transfer/clearing, and both final rewinds
are actual code. No tape reset, bulk copy, or head positioning is free. -/
def prepareTapes : Program :=
  packInput.asSubroutine 0 23 ++
    (rewindRegion .output).asSubroutine 23 34 ++
    transferPackedInput.asSubroutine 34 63 ++
    (rewindRegion .input).asSubroutine 63 74 ++
    (rewindRegion .output).asSubroutine 74 85 ++ [.halt]

/-- A guarded representation of the initial source tapes, with explicit
outer logical blanks. The old raw input and caller prefix are retained
beyond the input guard. This record states the postcondition only. -/
def prepareTapesFinish (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) : Configuration :=
  { pc := 85,
    inputTape := encodeTape (input.reverse.map some ++ beforeInput) (packedLogicalInput input),
    outputTape := encodeTape beforeOutput (rewoundTape { left := List.replicate input.length none }),
    halted := true }

/-- The complete initialization costs exactly `31*m + 42` native
transitions, independent of saved caller data and including the final halt. -/
theorem prepareTapes_runs (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    RunsFor prepareTapes (packInputStart beforeInput beforeOutput input)
      (prepareTapesFinish beforeInput beforeOutput input) (31 * input.length + 42) := by
  let a := packInput.asSubroutine 0 23
  let b := (rewindRegion .output).asSubroutine 23 34
  let c := transferPackedInput.asSubroutine 34 63
  let d := (rewindRegion .input).asSubroutine 63 74
  let e := (rewindRegion .output).asSubroutine 74 85
  let savedInput := input.reverse.map some ++ beforeInput
  have hPack := (packInput_runs beforeInput beforeOutput input).withSubroutine_halted_of_closed
    [] packInput (b ++ c ++ d ++ e ++ [.halt]) 23
    (by simp [packInputStart, packInput]) rfl rfl packInput_control_closed
  change RunsFor prepareTapes (packInputStart beforeInput beforeOutput input)
    ((packInputFinish beforeInput beforeOutput input).resumeAt 23) (7 * input.length + 10) at hPack
  have hFirstRewind := (rewindRegion_runs .output beforeOutput
      { left := input.reverse.map some } { left := savedInput }).withSubroutine_halted_of_closed
    a (rewindRegion .output) (c ++ d ++ e ++ [.halt]) 34
    (by simp [rewindRegionStart, start, rewindRegion]) rfl rfl (rewindRegion_control_closed .output)
  change RunsFor prepareTapes ((packInputFinish beforeInput beforeOutput input).resumeAt 23)
    ((transferPackedInputStart savedInput beforeOutput input).rebasePc 34)
    (rewindRegionSteps (input.reverse.map some)) at hFirstRewind
  rw [rewindRegionSteps_bits, List.length_reverse] at hFirstRewind
  have hTransfer := (transferPackedInput_runs savedInput beforeOutput input).withSubroutine_halted_of_closed
    (a ++ b) transferPackedInput (d ++ e ++ [.halt]) 63
    (by simp [transferPackedInputStart, transferPackedInput]) rfl rfl transferPackedInput_control_closed
  change RunsFor prepareTapes ((transferPackedInputStart savedInput beforeOutput input).rebasePc 34)
    ((transferPackedInputFinish savedInput beforeOutput input).resumeAt 63)
    (11 * input.length + 10) at hTransfer
  have hInputRewind := (rewindRegion_runs .input savedInput
      { left := input.reverse.map some }
      (encodeTape beforeOutput { left := List.replicate input.length none })).withSubroutine_halted_of_closed
    (a ++ b ++ c) (rewindRegion .input) (e ++ [.halt]) 74
    (by simp [rewindRegionStart, start, rewindRegion]) rfl rfl (rewindRegion_control_closed .input)
  change RunsFor prepareTapes ((transferPackedInputFinish savedInput beforeOutput input).resumeAt 63)
    ((rewindRegionStart .output beforeOutput { left := List.replicate input.length none }
      (encodeTape savedInput (packedLogicalInput input))).rebasePc 74)
    (rewindRegionSteps (input.reverse.map some)) at hInputRewind
  rw [rewindRegionSteps_bits, List.length_reverse] at hInputRewind
  have hOutputRewind := (rewindRegion_runs .output beforeOutput
      { left := List.replicate input.length none }
      (encodeTape savedInput (packedLogicalInput input))).withSubroutine_halted_of_closed
    (a ++ b ++ c ++ d) (rewindRegion .output) [.halt] 85
    (by simp [rewindRegionStart, start, rewindRegion]) rfl rfl (rewindRegion_control_closed .output)
  change RunsFor prepareTapes
    ((rewindRegionStart .output beforeOutput { left := List.replicate input.length none }
      (encodeTape savedInput (packedLogicalInput input))).rebasePc 74)
    ((prepareTapesFinish beforeInput beforeOutput input).resumeAt 85)
    (rewindRegionSteps (List.replicate input.length none)) at hOutputRewind
  rw [rewindRegionSteps_blanks] at hOutputRewind
  have hHalt : Step prepareTapes ((prepareTapesFinish beforeInput beforeOutput input).resumeAt 85)
      (prepareTapesFinish beforeInput beforeOutput input) := by
    simp [Step, successors, next, prepareTapes, packInput, transferPackedInput, rewindRegion,
      Program.asSubroutine, Instruction.asSubroutine, prepareTapesFinish,
      Configuration.resumeAt, Instruction.next]
  convert RunsFor.succ
    ((((hPack.trans hFirstRewind).trans hTransfer).trans hInputRewind).trans hOutputRewind)
    hHalt using 1; omega

theorem prepareTapes_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareTapes := by
  simp [prepareTapes, packInput, transferPackedInput, rewindRegion,
    Program.asSubroutine, Instruction.asSubroutine]

set_option maxHeartbeats 800000 in
theorem prepareTapes_control_closed (c d : Configuration)
    (hPc : c.pc < prepareTapes.length) (step : Step prepareTapes c d)
    (_hRunning : d.halted = false) : d.pc < prepareTapes.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 86 at hPc
  change d.pc < 86
  interval_cases hIndex : c.pc
  all_goals
    simp [Step, successors, next, hActive, hIndex, prepareTapes, packInput,
      transferPackedInput, rewindRegion, Program.asSubroutine, Instruction.asSubroutine,
      Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance,
    Configuration.updateTape, hIndex]

theorem prepareTapes_eval (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin prepareTapes (packInputStart beforeInput beforeOutput input)
      (31 * input.length + 42) = PMF.pure (prepareTapesFinish beforeInput beforeOutput input) :=
  (prepareTapes_runs beforeInput beforeOutput input).evalConfigWithin_eq_pure_of_no_randomBit
    prepareTapes_no_randomBit

theorem prepareTapes_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin (Program.withSubroutine pre prepareTapes suffix returnPc)
      ((packInputStart beforeInput beforeOutput input).rebasePc pre.length)
      (31 * input.length + 42) =
      PMF.pure ((prepareTapesFinish beforeInput beforeOutput input).resumeAt returnPc) :=
  (prepareTapes_runs beforeInput beforeOutput input).evalConfigWithin_withSubroutine_halted_of_closed
    pre prepareTapes suffix returnPc (by simp [packInputStart, prepareTapes]) rfl rfl
    prepareTapes_control_closed prepareTapes_no_randomBit

theorem prepareTapes_haltsWithin (input : List Bool) :
    HaltsWithin prepareTapes input (31 * input.length + 42) := by
  intro final run
  have hInitial : packInputStart [] [] input = Configuration.initial input := by cases input <;> rfl
  rw [← hInitial] at run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareTapes_eval] at hMem
  have hFinal : final = prepareTapesFinish [] [] input := by simpa using hMem
  subst final
  rfl

theorem prepareTapes_polynomialTime : PolynomialTime prepareTapes := by
  refine ⟨fun m => 31 * m + 42, ?_, prepareTapes_haltsWithin⟩
  exact ((PolynomiallyBounded.const 31).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 42)

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

theorem packedLogicalInput_equivalent (input : List Bool) :
    (packedLogicalInput input).Equivalent (Tape.ofBits input) := by
  cases input with
  | nil => exact Tape.Equivalent.refl _
  | cons bit rest =>
      rw [packedLogicalInput_cons]
      exact ⟨rfl, fun _ => rfl, getD_append_blank (rest.map some)⟩

theorem rewound_blank_region (count : Nat) :
    rewoundTape { left := List.replicate count none } =
      ({ right := List.replicate count none } : Tape) := by
  simp only [rewoundTape, List.reverse_replicate]
  rw [← List.replicate_succ', List.replicate_succ]

/-- Logical source state actually represented by `prepareTapesFinish`.
Its redundant blank cells are retained, rather than removed during execution. -/
def preparedSource (input : List Bool) : Configuration :=
  { inputTape := packedLogicalInput input,
    outputTape := rewoundTape { left := List.replicate input.length none } }

theorem prepareTapesFinish_represents_source (programLength : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    (prepareTapesFinish beforeInput beforeOutput input).resumeAt 0 =
      encodeConfiguration programLength (input.reverse.map some ++ beforeInput)
        beforeOutput (preparedSource input) := rfl

theorem preparedSource_equivalent_initial (input : List Bool) :
    (preparedSource input).Equivalent (Configuration.initial input) := by
  refine ⟨rfl, rfl, packedLogicalInput_equivalent input, ?_⟩
  change (rewoundTape { left := List.replicate input.length none }).Equivalent ({} : Tape)
  rw [rewound_blank_region]
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro i
  simp only [List.getD, List.getElem?_replicate]
  split <;> rfl

/-- All original random branches also halt from the prepared logical
state. Cell equivalence transfers the bound without performing any reset. -/
theorem preparedSource_all_branches_halted (source : Program) (input : List Bool)
    (steps : Nat) (halts : HaltsWithin source input steps) :
    ∀ final, PaddedRunsFor source (preparedSource input) final steps → final.halted = true :=
  halts.of_equivalent_initial (preparedSource_equivalent_initial input).symm

/-- Preparing tapes preserves the source's output distribution, including
timeout, under the original operational semantics and transition budget. -/
theorem preparedSource_evalOutput (source : Program) (input : List Bool) (steps : Nat) :
    (evalConfigWithin source (preparedSource input) steps).map
        (fun c => if c.halted then some c.outputBits else none) =
      evalWithin source input steps :=
  (preparedSource_equivalent_initial input).evalOutput source steps

end Machine.GuardedCompiler
