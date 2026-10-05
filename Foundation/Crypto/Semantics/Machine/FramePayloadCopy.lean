import Foundation.Crypto.Semantics.Machine.FramedInput

namespace Machine.FramePayloadCopy

/-- Copy a unary-length frame payload onto the output tape. The counter is
kept on the output tape while the input head crosses the payload, then its
cells are overwritten from right to left. A final synchronized scan restores
both heads to the cells after the payload. No list operation is an instruction. -/
def program : Program :=
  [.branch .input 29 5 1,
   .write .output true, .moveRight .input, .moveRight .output, .jump 0,
   .moveRight .input, .moveLeft .output,
   .branch .output 11 8 8,
   .moveRight .input, .moveLeft .output, .jump 7,
   .moveRight .output,
   .branch .output 15 13 13,
   .moveRight .output, .jump 12,
   .moveLeft .output,
   .branch .output 24 17 17,
   .moveLeft .input,
   .branch .input 19 19 21,
   .write .output false, .jump 22,
   .write .output true,
   .moveLeft .output, .jump 16,
   .moveRight .output,
   .branch .output 29 26 26,
   .moveRight .input, .moveRight .output, .jump 25,
   .halt]

private def headerState (before : List (Option Bool))
    (copied : Nat) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with
      left := List.replicate copied (some true) ++ before },
    outputTape := { left := List.replicate copied (some true) } }

private def counterTape : Nat → Nat → Tape
  | 0, copied => { right := List.replicate copied (some true) ++ [none] }
  | remaining + 1, copied =>
      { left := List.replicate remaining (some true), current := some true,
        right := List.replicate copied (some true) ++ [none] }

private def headerFinish (before : List (Option Bool))
    (count : Nat) (rest : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { Tape.ofBits rest with
      left := some false :: List.replicate count (some true) ++ before },
    outputTape := counterTape count 0 }

private theorem header_one (before : List (Option Bool))
    (copied : Nat) (rest : List Bool) :
    RunsFor program (headerState before copied (true :: rest))
      (headerState before (copied + 1) rest) 5 := by
  let start := headerState before copied (true :: rest)
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration :=
    { selected with pc := 2, outputTape := selected.outputTape.write (some true) }
  let movedInput : Configuration :=
    { written with pc := 3, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, headerState,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written, headerState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step program written movedInput := by
    simp [Step, successors, next, program, start, selected, written, movedInput,
      headerState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, start, selected, written,
      movedInput, movedOutput, headerState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput (headerState before (copied + 1) rest) := by
    cases rest <;> simp [Step, successors, next, program, start, selected,
      written, movedInput, movedOutput, headerState, Instruction.next,
      Tape.moveRight, Tape.write, Tape.ofBits, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hWrite) hInput) hOutput) hBack

private theorem header_end (before : List (Option Bool))
    (count : Nat) (rest : List Bool) :
    RunsFor program
      (headerState before count (false :: rest))
      (headerFinish before count rest) 3 := by
  let start := headerState before count (false :: rest)
  let selected : Configuration := { start with pc := 5 }
  let movedInput : Configuration :=
    { selected with pc := 6, inputTape := selected.inputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, headerState,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      headerState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput (headerFinish before count rest) := by
    cases count <;> cases rest <;>
      simp [Step, successors, next, program, start, selected, movedInput,
        headerState, headerFinish, counterTape, Instruction.next,
        Configuration.updateTape, Configuration.advance, Tape.moveRight,
        Tape.moveLeft, Tape.ofBits, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch)
    hInput) hOutput

private theorem header_run (before : List (Option Bool))
    (count copied : Nat) (rest : List Bool) :
    RunsFor program
      (headerState before copied (List.replicate count true ++ false :: rest))
      (headerFinish before (copied + count) rest)
      (5 * count + 3) := by
  induction count generalizing copied with
  | zero =>
      simpa using header_end before copied rest
  | succ count ih =>
      have first := header_one before copied (List.replicate count true ++ false :: rest)
      have tail := ih (copied + 1)
      have hCount : copied + 1 + count = copied + (count + 1) := by omega
      rw [hCount] at tail
      convert first.trans tail using 1
      · simp [List.replicate_succ]
      · omega

private def scanState (beforeHeader : List (Option Bool))
    (processed remaining rest : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { Tape.ofBits (remaining ++ rest) with
      left := processed.reverse.map some ++ beforeHeader },
    outputTape := counterTape remaining.length processed.length }

private theorem counterTape_moveLeft (remaining copied : Nat) :
    (counterTape (remaining + 1) copied).moveLeft =
      counterTape remaining (copied + 1) := by
  cases remaining <;>
    simp [counterTape, Tape.moveLeft, List.replicate_succ]

private theorem scan_one (beforeHeader : List (Option Bool))
    (processed remaining rest : List Bool) (bit : Bool) :
    RunsFor program
      (scanState beforeHeader processed (bit :: remaining) rest)
      (scanState beforeHeader (processed ++ [bit]) remaining rest) 4 := by
  let start := scanState beforeHeader processed (bit :: remaining) rest
  let selected : Configuration := { start with pc := 8 }
  let movedInput : Configuration :=
    { selected with pc := 9, inputTape := selected.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 10, outputTape := movedInput.outputTape.moveLeft }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, scanState,
      counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      scanState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, scanState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hBack : Step program movedOutput
      (scanState beforeHeader (processed ++ [bit]) remaining rest) := by
    cases hTail : remaining ++ rest <;>
      simp [Step, successors, next, program, start, selected, movedInput,
        movedOutput, scanState, Instruction.next, Tape.moveRight,
        counterTape_moveLeft, List.reverse_append, hTail, Tape.ofBits]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hInput) hOutput) hBack

private theorem scan_end (beforeHeader : List (Option Bool))
    (processed rest : List Bool) :
    RunsFor program (scanState beforeHeader processed [] rest)
      { scanState beforeHeader processed [] rest with pc := 11 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, scanState,
    counterTape, Instruction.next, Configuration.tape]

private theorem scan_run (beforeHeader : List (Option Bool))
    (processed remaining rest : List Bool) :
    RunsFor program (scanState beforeHeader processed remaining rest)
      { scanState beforeHeader (processed ++ remaining) [] rest with pc := 11 }
      (4 * remaining.length + 1) := by
  induction remaining generalizing processed with
  | nil => simpa using scan_end beforeHeader processed rest
  | cons bit remaining ih =>
      have first := scan_one beforeHeader processed remaining rest bit
      have tail := ih (processed ++ [bit])
      have hSteps : 4 + (4 * remaining.length + 1) =
          4 * (bit :: remaining).length + 1 := by simp; omega
      simpa [List.append_assoc, hSteps] using first.trans tail

private def forwardTape : Nat → Nat → Tape
  | 0, passed =>
      { left := List.replicate passed (some true) ++ [none] }
  | remaining + 1, passed =>
      { left := List.replicate passed (some true) ++ [none],
        current := some true,
        right := List.replicate remaining (some true) ++ [none] }

private def copyTape : Nat → List Bool → Tape
  | 0, copied => { right := copied.map some ++ [none] }
  | remaining + 1, copied =>
      { left := List.replicate remaining (some true) ++ [none],
        current := some true,
        right := copied.map some ++ [none] }

private def seekState (input : Tape) (remaining passed : Nat) : Configuration :=
  { pc := 12, inputTape := input, outputTape := forwardTape remaining passed }

private theorem counterTape_moveRight (count : Nat) :
    (counterTape 0 count).moveRight = forwardTape count 0 := by
  cases count <;>
    simp [counterTape, forwardTape, Tape.moveRight, List.replicate_succ]

private theorem seek_start (input : Tape) (count : Nat) :
    RunsFor program
      ({ pc := 11, inputTape := input, outputTape := counterTape 0 count } : Configuration)
      (seekState input count 0) 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, seekState, counterTape_moveRight,
    Instruction.next, Configuration.updateTape, Configuration.advance]

private theorem forwardTape_moveRight (remaining passed : Nat) :
    (forwardTape (remaining + 1) passed).moveRight =
      forwardTape remaining (passed + 1) := by
  cases remaining <;>
    simp [forwardTape, Tape.moveRight, List.replicate_succ]

private theorem seek_one (input : Tape) (remaining passed : Nat) :
    RunsFor program (seekState input (remaining + 1) passed)
      (seekState input remaining (passed + 1)) 3 := by
  let start := seekState input (remaining + 1) passed
  let selected : Configuration := { start with pc := 13 }
  let moved : Configuration :=
    { selected with pc := 14, outputTape := selected.outputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, seekState,
      forwardTape, Instruction.next, Configuration.tape]
  have hMove : Step program selected moved := by
    simp [Step, successors, next, program, start, selected, moved,
      seekState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step program moved (seekState input remaining (passed + 1)) := by
    simp [Step, successors, next, program, start, selected, moved,
      seekState, forwardTape_moveRight, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch)
    hMove) hBack

private theorem forwardTape_moveLeft (count : Nat) :
    (forwardTape 0 count).moveLeft = copyTape count [] := by
  cases count <;>
    simp [forwardTape, copyTape, Tape.moveLeft, List.replicate_succ]

private theorem seek_end (input : Tape) (count : Nat) :
    RunsFor program (seekState input 0 count)
      ({ pc := 16, inputTape := input, outputTape := copyTape count [] } : Configuration)
      2 := by
  let start := seekState input 0 count
  let selected : Configuration := { start with pc := 15 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, seekState,
      forwardTape, Instruction.next, Configuration.tape]
  have hMove : Step program selected
      ({ pc := 16, inputTape := input, outputTape := copyTape count [] } : Configuration) := by
    simp [Step, successors, next, program, start, selected, seekState,
      forwardTape_moveLeft, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hMove

private theorem seek_run (input : Tape) (remaining passed : Nat) :
    RunsFor program (seekState input remaining passed)
      ({ pc := 16, inputTape := input,
         outputTape := copyTape (passed + remaining) [] } : Configuration)
      (3 * remaining + 2) := by
  induction remaining generalizing passed with
  | zero => simpa using seek_end input passed
  | succ remaining ih =>
      have first := seek_one input remaining passed
      have tail := ih (passed + 1)
      have hCount : passed + 1 + remaining = passed + (remaining + 1) := by omega
      rw [hCount] at tail
      convert first.trans tail using 1
      omega

private def backInput : Tape → Nat → Tape
  | input, 0 => input
  | input, count + 1 => backInput input.moveLeft count

private def copyState (input : Tape) (remaining : Nat)
    (copied : List Bool) : Configuration :=
  { pc := 16, inputTape := input, outputTape := copyTape remaining copied }

private theorem copyTape_write_moveLeft (remaining : Nat)
    (copied : List Bool) (bit : Bool) :
    ((copyTape (remaining + 1) copied).write (some bit)).moveLeft =
      copyTape remaining (bit :: copied) := by
  cases remaining <;>
    simp [copyTape, Tape.write, Tape.moveLeft, List.replicate_succ]

private def copyOneSteps (bit : Bool) : Nat := if bit then 6 else 7

private theorem copy_one (input : Tape) (remaining : Nat)
    (copied : List Bool) (bit : Bool) (before : List (Option Bool))
    (hLeft : input.left = some bit :: before) :
    RunsFor program (copyState input (remaining + 1) copied)
      (copyState input.moveLeft remaining (bit :: copied))
      (copyOneSteps bit) := by
  let start := copyState input (remaining + 1) copied
  let selected : Configuration := { start with pc := 17 }
  let movedInput : Configuration :=
    { selected with pc := 18, inputTape := selected.inputTape.moveLeft }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, copyState,
      copyTape, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      copyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  cases bit with
  | false =>
      let chosen : Configuration := { movedInput with pc := 19 }
      let written : Configuration :=
        { chosen with pc := 20, outputTape := chosen.outputTape.write (some false) }
      let jumped : Configuration := { written with pc := 22 }
      let movedOutput : Configuration :=
        { jumped with pc := 23, outputTape := jumped.outputTape.moveLeft }
      have hChoose : Step program movedInput chosen := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, copyState, Tape.moveLeft, hLeft, Instruction.next,
          Configuration.tape]
      have hWrite : Step program chosen written := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, copyState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hJump : Step program written jumped := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, jumped, copyState,
          Instruction.next]
      have hOutput : Step program jumped movedOutput := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, jumped, movedOutput, copyState,
          Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBack : Step program movedOutput
          (copyState input.moveLeft remaining (false :: copied)) := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, jumped, movedOutput, copyState,
          copyTape_write_moveLeft, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _)
          hBranch) hInput) hChoose) hWrite) hJump) hOutput) hBack
  | true =>
      let chosen : Configuration := { movedInput with pc := 21 }
      let written : Configuration :=
        { chosen with pc := 22, outputTape := chosen.outputTape.write (some true) }
      let movedOutput : Configuration :=
        { written with pc := 23, outputTape := written.outputTape.moveLeft }
      have hChoose : Step program movedInput chosen := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, copyState, Tape.moveLeft, hLeft, Instruction.next,
          Configuration.tape]
      have hWrite : Step program chosen written := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, copyState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hOutput : Step program written movedOutput := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, movedOutput, copyState,
          Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBack : Step program movedOutput
          (copyState input.moveLeft remaining (true :: copied)) := by
        simp [Step, successors, next, program, start, selected, movedInput,
          chosen, written, movedOutput, copyState,
          copyTape_write_moveLeft, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _)
          hBranch) hInput) hChoose) hWrite) hOutput) hBack

private theorem copy_end (input : Tape) (copied : List Bool) :
    RunsFor program (copyState input 0 copied)
      { copyState input 0 copied with pc := 24 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, copyState, copyTape,
    Instruction.next, Configuration.tape]

private theorem copy_run (input : Tape) (beforeHeader : List (Option Bool))
    (remaining copied : List Bool)
    (hLeft : input.left = remaining.reverse.map some ++ beforeHeader) :
    ∃ used, used ≤ 7 * remaining.length + 1 ∧
      RunsFor program (copyState input remaining.length copied)
        { pc := 24, inputTape := backInput input remaining.length,
          outputTape := copyTape 0 (remaining ++ copied) } used := by
  induction remaining using List.reverseRecOn generalizing input copied with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      simpa [copyState, backInput] using copy_end input copied
  | append_singleton initialBits bit ih =>
      have hFirst : input.left = some bit ::
          (initialBits.reverse.map some ++ beforeHeader) := by
        simpa [List.reverse_append, List.map_append] using hLeft
      have hNext : input.moveLeft.left =
          initialBits.reverse.map some ++ beforeHeader := by
        simp [Tape.moveLeft, hFirst]
      have first := copy_one input initialBits.length copied bit _ hFirst
      obtain ⟨tailSteps, hTailSteps, tail⟩ :=
        ih input.moveLeft (bit :: copied) hNext
      refine ⟨copyOneSteps bit + tailSteps, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        have hOne : copyOneSteps bit ≤ 7 := by cases bit <;> decide
        omega
      · simpa [copyState, List.length_append, backInput,
          List.append_assoc] using first.trans tail

private def forwardInput : Tape → Nat → Tape
  | input, 0 => input
  | input, count + 1 => forwardInput input.moveRight count

private theorem forwardInput_succ (input : Tape) (count : Nat) :
    forwardInput input (count + 1) =
      (forwardInput input count).moveRight := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
      simpa [forwardInput] using ih input.moveRight

private theorem forwardInput_suffix (before : List (Option Bool))
    (bits : List Bool) (count : Nat) :
    ∃ left : List (Option Bool),
      forwardInput ({ Tape.ofBits bits with left := before } : Tape) count =
        { Tape.ofBits (bits.drop count) with left := left } := by
  induction count generalizing before bits with
  | zero => exact ⟨before, rfl⟩
  | succ count ih =>
      cases bits with
      | nil => simpa [forwardInput, Tape.ofBits, Tape.moveRight] using
          (ih (none :: before) [])
      | cons bit rest =>
          cases rest with
          | nil => simpa [forwardInput, Tape.ofBits, Tape.moveRight] using
              (ih (some bit :: before) [])
          | cons next tail =>
              simpa [forwardInput, Tape.ofBits, Tape.moveRight] using
                (ih (some bit :: before) (next :: tail))

private def scanOutput (passed remaining : List Bool) : Tape :=
  match remaining with
  | [] => { left := passed.reverse.map some ++ [none] }
  | bit :: rest =>
      { left := passed.reverse.map some ++ [none], current := some bit,
        right := rest.map some ++ [none] }

private def forwardState (input : Tape) (passed remaining : List Bool) :
    Configuration :=
  { pc := 25,
    inputTape := forwardInput input passed.length,
    outputTape := scanOutput passed remaining }

private theorem scanOutput_moveRight (passed remaining : List Bool)
    (bit : Bool) :
    (scanOutput passed (bit :: remaining)).moveRight =
      scanOutput (passed ++ [bit]) remaining := by
  cases remaining <;>
    simp [scanOutput, Tape.moveRight, List.reverse_append]

private theorem forward_start (input : Tape) (bits : List Bool) :
    RunsFor program (copyState input 0 bits)
      (forwardState input [] bits) 2 := by
  let start := copyState input 0 bits
  let selected : Configuration := { start with pc := 24 }
  have hEnd : Step program start selected := by
    simp [Step, successors, next, program, start, selected, copyState,
      copyTape, Instruction.next, Configuration.tape]
  have hOutput : Step program selected (forwardState input [] bits) := by
    cases bits <;>
      simp [Step, successors, next, program, start, selected, copyState,
        copyTape, forwardState, forwardInput, scanOutput, Tape.moveRight,
        Instruction.next, Configuration.updateTape, Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hEnd) hOutput

private theorem forward_init (input : Tape) (bits : List Bool) :
    RunsFor program
      ({ pc := 24, inputTape := input, outputTape := copyTape 0 bits } : Configuration)
      (forwardState input [] bits) 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  cases bits <;>
    simp [Step, successors, next, program, forwardState, forwardInput,
      scanOutput, copyTape, Tape.moveRight, Instruction.next,
      Configuration.updateTape, Configuration.advance]

private theorem forward_one (input : Tape) (passed remaining : List Bool)
    (bit : Bool) :
    RunsFor program (forwardState input passed (bit :: remaining))
      (forwardState input (passed ++ [bit]) remaining) 4 := by
  let start := forwardState input passed (bit :: remaining)
  let selected : Configuration := { start with pc := 26 }
  let movedInput : Configuration :=
    { selected with pc := 27, inputTape := selected.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 28, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    cases bit <;>
      simp [Step, successors, next, program, start, selected, forwardState,
      scanOutput, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      forwardState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, forwardState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (forwardState input (passed ++ [bit]) remaining) := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, forwardState, scanOutput_moveRight,
      forwardInput_succ, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hInput) hOutput) hBack

private theorem forward_end (input : Tape) (passed : List Bool) :
    RunsFor program (forwardState input passed [])
      { forwardState input passed [] with pc := 29 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, forwardState, scanOutput,
    Instruction.next, Configuration.tape]

private theorem forward_run (input : Tape) (passed remaining : List Bool) :
    RunsFor program (forwardState input passed remaining)
      { forwardState input (passed ++ remaining) [] with pc := 29 }
      (4 * remaining.length + 1) := by
  induction remaining generalizing passed with
  | nil => simpa using forward_end input passed
  | cons bit remaining ih =>
      have first := forward_one input passed remaining bit
      have tail := ih (passed ++ [bit])
      have hSteps : 4 + (4 * remaining.length + 1) =
          4 * (bit :: remaining).length + 1 := by simp; omega
      simpa [List.append_assoc, hSteps] using first.trans tail

private theorem moveLeft_moveRight_of_left (input : Tape)
    (cell : Option Bool) (before : List (Option Bool))
    (hLeft : input.left = cell :: before) :
    input.moveLeft.moveRight = input := by
  cases input with
  | mk left current right =>
      simp only at hLeft
      subst left
      simp [Tape.moveLeft, Tape.moveRight]

private theorem forward_back (input : Tape) (cells before : List (Option Bool))
    (hLeft : input.left = cells ++ before) :
    forwardInput (backInput input cells.length) cells.length = input := by
  induction cells generalizing input with
  | nil => simp [backInput, forwardInput]
  | cons cell cells ih =>
      have hCurrent : input.left = cell :: (cells ++ before) := by
        simpa using hLeft
      have hNext : input.moveLeft.left = cells ++ before := by
        simp [Tape.moveLeft, hCurrent]
      have hInv := moveLeft_moveRight_of_left input cell
        (cells ++ before) hCurrent
      simpa [backInput, forwardInput_succ, ih input.moveLeft hNext]
        using hInv

private theorem forward_final_input (rest bits : List Bool)
    (beforeHeader : List (Option Bool)) :
    forwardInput
      (backInput (scanState beforeHeader bits [] rest).inputTape bits.length)
      bits.length = (scanState beforeHeader bits [] rest).inputTape := by
  have hLeft : (scanState beforeHeader bits [] rest).inputTape.left =
      bits.reverse.map some ++ beforeHeader := by rfl
  simpa using forward_back _ (bits.reverse.map some) beforeHeader hLeft

private theorem halt_final (input : Tape) (bits : List Bool) :
    Step program
      { forwardState input bits [] with pc := 29 }
      { forwardState input bits [] with pc := 29, halted := true } := by
  simp [Step, successors, next, program, forwardState,
    Instruction.next]

private theorem headerFinish_eq_scanState (before : List (Option Bool))
    (bits rest : List Bool) :
    headerFinish before bits.length (bits ++ rest) =
      scanState (some false :: List.replicate bits.length (some true) ++ before)
        [] bits rest := by
  simp [headerFinish, scanState]

private theorem scanFinish_eq_seekStart (beforeHeader : List (Option Bool))
    (bits rest : List Bool) :
    { scanState beforeHeader bits [] rest with pc := 11 } =
      ({ pc := 11, inputTape := (scanState beforeHeader bits [] rest).inputTape,
         outputTape := counterTape 0 bits.length } : Configuration) := by
  simp [scanState]

/-- On a well-formed unary-length frame, the fixed finite code copies exactly
the payload, leaves the input head after it, and halts in linear time. -/
theorem runs_valid (before : List (Option Bool)) (bits rest : List Bool) :
    ∃ target used, used ≤ 23 * bits.length + 11 ∧
      RunsFor program
        { inputTape := { Tape.ofBits (frame bits ++ rest) with left := before } }
        target used ∧
      target.halted = true ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := bits.reverse.map some ++
            some false :: List.replicate bits.length (some true) ++ before } ∧
      target.outputTape =
        { left := bits.reverse.map some ++ [none] } ∧
      target.outputTape.bits = bits := by
  let bh := some false :: List.replicate bits.length (some true) ++ before
  let input := (scanState bh bits [] rest).inputTape
  let final :=
    ({ forwardState (backInput input bits.length) bits [] with
       pc := 29, halted := true } : Configuration)
  have r1 := header_run before bits.length 0 (bits ++ rest)
  have r2 := scan_run bh [] bits rest
  have r3 := seek_start input bits.length
  have r4 := seek_run input bits.length 0
  have hLeft : input.left = bits.reverse.map some ++ bh := by rfl
  obtain ⟨copySteps, hCopySteps, r5⟩ :=
    copy_run input bh bits [] hLeft
  have r6 := forward_init (backInput input bits.length) bits
  have r7 := forward_run (backInput input bits.length) [] bits
  have r8 : RunsFor program
      ({ forwardState (backInput input bits.length) bits [] with pc := 29 } : Configuration)
      final 1 := by
    exact RunsFor.succ (RunsFor.zero _) (halt_final _ _)
  have r12 : RunsFor program
      (headerState before 0 (frame bits ++ rest))
      { scanState bh bits [] rest with pc := 11 }
      ((5 * bits.length + 3) + (4 * bits.length + 1)) := by
    have r1' : RunsFor program
        (headerState before 0 (frame bits ++ rest))
        (scanState bh [] bits rest) (5 * bits.length + 3) := by
      simpa [frame, bh, headerFinish_eq_scanState, List.append_assoc]
        using r1
    simpa using r1'.trans r2
  have r34 : RunsFor program
      ({ scanState bh bits [] rest with pc := 11 } : Configuration)
      ({ pc := 16, inputTape := input, outputTape := copyTape bits.length [] } : Configuration)
      (1 + (3 * bits.length + 2)) := by
    simpa [input, scanFinish_eq_seekStart, seekState] using r3.trans r4
  have r56 : RunsFor program
      ({ pc := 16, inputTape := input, outputTape := copyTape bits.length [] } : Configuration)
      (forwardState (backInput input bits.length) [] bits)
      (copySteps + 1) := by
    have r5' : RunsFor program
        (copyState input bits.length [])
        ({ pc := 24, inputTape := backInput input bits.length,
           outputTape := copyTape 0 bits } : Configuration) copySteps := by
      simpa using r5
    simpa [copyState] using r5'.trans r6
  have r78 : RunsFor program
      (forwardState (backInput input bits.length) [] bits)
      final ((4 * bits.length + 1) + 1) := by
    simpa [final] using r7.trans r8
  have run := ((r12.trans r34).trans r56).trans r78
  refine ⟨final,
    (5 * bits.length + 3) + (4 * bits.length + 1) +
      (1 + (3 * bits.length + 2)) + (copySteps + 1) +
      ((4 * bits.length + 1) + 1), ?_, ?_, rfl, ?_, ?_, ?_⟩
  · omega
  · simpa [headerState] using run
  · have hInput := forward_final_input rest bits bh
    simpa [final, forwardState, input, bh, scanState,
      List.map_reverse, List.append_assoc] using hInput
  · rfl
  · simp [final, forwardState, scanOutput, Tape.bits]

private def scanAnyState (input : Tape) (remaining copied : Nat) : Configuration :=
  { pc := 7, inputTape := input, outputTape := counterTape remaining copied }

private theorem scanAny_one (input : Tape) (remaining copied : Nat) :
    RunsFor program (scanAnyState input (remaining + 1) copied)
      (scanAnyState input.moveRight remaining (copied + 1)) 4 := by
  let start := scanAnyState input (remaining + 1) copied
  let selected : Configuration := { start with pc := 8 }
  let movedInput : Configuration :=
    { selected with pc := 9, inputTape := selected.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 10, outputTape := movedInput.outputTape.moveLeft }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, scanAnyState,
      counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      scanAnyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, scanAnyState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (scanAnyState input.moveRight remaining (copied + 1)) := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, scanAnyState, counterTape_moveLeft, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hInput) hOutput) hBack

private theorem scanAny_end (input : Tape) (copied : Nat) :
    RunsFor program (scanAnyState input 0 copied)
      { scanAnyState input 0 copied with pc := 11 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, scanAnyState,
    counterTape, Instruction.next, Configuration.tape]

private theorem scanAny_run (input : Tape) (remaining copied : Nat) :
    RunsFor program (scanAnyState input remaining copied)
      { scanAnyState (forwardInput input remaining) 0 (copied + remaining) with
        pc := 11 } (4 * remaining + 1) := by
  induction remaining generalizing input copied with
  | zero => simpa [forwardInput] using scanAny_end input copied
  | succ remaining ih =>
      have first := scanAny_one input remaining copied
      have tail := ih input.moveRight (copied + 1)
      have hCount : copied + 1 + remaining = copied + (remaining + 1) := by omega
      rw [hCount] at tail
      convert first.trans tail using 1
      · simp [forwardInput]
      · omega

private theorem forwardInput_left_length (input : Tape) (count : Nat) :
    count ≤ (forwardInput input count).left.length := by
  induction count with
  | zero => omega
  | succ count ih =>
      have hGrow : (forwardInput input (count + 1)).left.length =
          (forwardInput input count).left.length + 1 := by
        cases hRight : (forwardInput input count).right <;>
          simp [forwardInput_succ, Tape.moveRight, hRight]
      omega

private theorem copy_blank (input : Tape) (remaining : Nat)
    (copied : List Bool) (before : List (Option Bool))
    (hLeft : input.left = none :: before) :
    RunsFor program (copyState input (remaining + 1) copied)
      (copyState input.moveLeft remaining (false :: copied)) 7 := by
  let start := copyState input (remaining + 1) copied
  let selected : Configuration := { start with pc := 17 }
  let movedInput : Configuration :=
    { selected with pc := 18, inputTape := selected.inputTape.moveLeft }
  let chosen : Configuration := { movedInput with pc := 19 }
  let written : Configuration :=
    { chosen with pc := 20, outputTape := chosen.outputTape.write (some false) }
  let jumped : Configuration := { written with pc := 22 }
  let movedOutput : Configuration :=
    { jumped with pc := 23, outputTape := jumped.outputTape.moveLeft }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, copyState,
      copyTape, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      copyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hChoose : Step program movedInput chosen := by
    simp [Step, successors, next, program, start, selected, movedInput,
      chosen, copyState, Tape.moveLeft, hLeft, Instruction.next,
      Configuration.tape]
  have hWrite : Step program chosen written := by
    simp [Step, successors, next, program, start, selected, movedInput,
      chosen, written, copyState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hJump : Step program written jumped := by
    simp [Step, successors, next, program, start, selected, movedInput,
      chosen, written, jumped, copyState, Instruction.next]
  have hOutput : Step program jumped movedOutput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      chosen, written, jumped, movedOutput, copyState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (copyState input.moveLeft remaining (false :: copied)) := by
    simp [Step, successors, next, program, start, selected, movedInput,
      chosen, written, jumped, movedOutput, copyState,
      copyTape_write_moveLeft, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _)
      hBranch) hInput) hChoose) hWrite) hJump) hOutput) hBack

private theorem copy_any_one (input : Tape) (remaining : Nat)
    (copied : List Bool) (cell : Option Bool) (before : List (Option Bool))
    (hLeft : input.left = cell :: before) :
    ∃ bit steps, steps ≤ 7 ∧
      RunsFor program (copyState input (remaining + 1) copied)
        (copyState input.moveLeft remaining (bit :: copied)) steps := by
  cases cell with
  | none => exact ⟨false, 7, Nat.le_refl _, copy_blank input remaining copied before hLeft⟩
  | some bit =>
      refine ⟨bit, copyOneSteps bit, ?_, copy_one input remaining copied bit before hLeft⟩
      cases bit <;> decide

private theorem copy_any_run (input : Tape) (count : Nat)
    (prefixBits : List Bool)
    (hLeft : count ≤ input.left.length) :
    ∃ copied used, copied.length = count + prefixBits.length ∧
      used ≤ 7 * count + 1 ∧
      RunsFor program (copyState input count prefixBits)
        { pc := 24, inputTape := backInput input count,
          outputTape := copyTape 0 copied } used := by
  induction count generalizing input prefixBits with
  | zero =>
      refine ⟨prefixBits, 1, by simp, by simp, ?_⟩
      simpa [copyState, backInput] using copy_end input prefixBits
  | succ count ih =>
      cases hCells : input.left with
      | nil => simp [hCells] at hLeft
      | cons cell before =>
          obtain ⟨bit, firstSteps, hFirstSteps, first⟩ :=
            copy_any_one input count prefixBits cell before hCells
          have hNext : count ≤ input.moveLeft.left.length := by
            simp [Tape.moveLeft, hCells] at *
            omega
          obtain ⟨copied, tailSteps, hLength, hTailSteps, tail⟩ :=
            ih input.moveLeft (bit :: prefixBits) hNext
          refine ⟨copied, firstSteps + tailSteps, ?_, ?_, ?_⟩
          · simp only [List.length_cons] at hLength
            omega
          · omega
          · simpa [copyState, backInput] using first.trans tail

private theorem header_blank (before : List (Option Bool))
    (copied : Nat) :
    RunsFor program (headerState before copied [])
      { headerState before copied [] with pc := 29, halted := true } 2 := by
  let start := headerState before copied []
  let selected : Configuration := { start with pc := 29 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected,
      headerState, Tape.ofBits, Instruction.next, Configuration.tape]
  have hHalt : Step program selected
      { headerState before copied [] with pc := 29, halted := true } := by
    simp [Step, successors, next, program, start, selected,
      headerState, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt

private theorem header_unterminated (before : List (Option Bool))
    (remaining copied : Nat) :
    RunsFor program (headerState before copied (List.replicate remaining true))
      { headerState before (copied + remaining) [] with pc := 29, halted := true }
      (5 * remaining + 2) := by
  induction remaining generalizing copied with
  | zero => simpa using header_blank before copied
  | succ remaining ih =>
      have first := header_one before copied (List.replicate remaining true)
      have tail := ih (copied + 1)
      have hCount : copied + 1 + remaining = copied + (remaining + 1) := by omega
      rw [hCount] at tail
      convert first.trans tail using 1
      · simp [List.replicate_succ]
      · omega

private theorem unary_split (input : List Bool) :
    (∃ count, input = List.replicate count true) ∨
      (∃ count rest, input = List.replicate count true ++ false :: rest) := by
  induction input with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit rest ih =>
      cases bit with
      | false => exact Or.inr ⟨0, rest, rfl⟩
      | true =>
          rcases ih with ⟨count, h⟩ | ⟨count, tail, h⟩
          · exact Or.inl ⟨count + 1, by simp [h, List.replicate_succ]⟩
          · exact Or.inr ⟨count + 1, tail, by simp [h, List.replicate_succ]⟩

/-- Adding a blank cell beyond the finite copied block does not change the
physical tape represented by the zipper. -/
theorem trailing_blank_equivalent (bits : List Bool) :
    ({ left := bits.reverse.map some } : Tape).Equivalent
      { left := bits.reverse.map some ++ [none] } := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  change (bits.reverse.map some).getD i none =
    ((bits.reverse.map some) ++ [none]).getD i none
  by_cases hi : i < (bits.reverse.map some).length
  · rw [List.getD_append _ _ _ _ hi]
  · have hlen : (bits.reverse.map some).length ≤ i := Nat.le_of_not_gt hi
    rw [List.getD_eq_default _ none hlen,
      List.getD_append_right _ _ _ _ hlen]
    simp

/-- Every finite input halts. The unary header bounds the later scans and
backward copy even when the payload ends before its advertised length. The
output still consists of one contiguous copied block followed by a blank. -/
theorem runs_any_from_layout (before : List (Option Bool)) (inputBits : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (copied : List Bool),
      used ≤ 23 * inputBits.length + 11 ∧
      RunsFor program
        { inputTape := { Tape.ofBits inputBits with left := before } }
        finish used ∧ finish.halted = true ∧
      finish.outputTape.Equivalent
        { left := copied.reverse.map some ++ [none] } ∧
      ∃ left rest, finish.inputTape = { Tape.ofBits rest with left := left } ∧
        rest.length ≤ inputBits.length := by
  rcases unary_split inputBits with ⟨count, hInput⟩ | ⟨count, rest, hInput⟩
  · subst inputBits
    have run := header_unterminated before count 0
    let finish : Configuration :=
      { headerState before (0 + count) [] with pc := 29, halted := true }
    refine ⟨finish, 5 * count + 2, List.replicate count true, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [List.length_replicate]
      omega
    · simpa [finish, headerState] using run
    · simpa [finish, headerState] using
        trailing_blank_equivalent (List.replicate count true)
    · refine ⟨List.replicate count (some true) ++ before, [], ?_, by simp⟩
      simp [finish, headerState]
  · subst inputBits
    let input := (headerFinish before count rest).inputTape
    let scanned := forwardInput input count
    have rHeader := header_run before count 0 rest
    have rScan := scanAny_run input count 0
    have rSeekStart := seek_start scanned count
    have rSeek := seek_run scanned count 0
    have hLeft : count ≤ scanned.left.length :=
      forwardInput_left_length input count
    obtain ⟨copied, copySteps, hCopied, hCopySteps, rCopy⟩ :=
      copy_any_run scanned count [] hLeft
    have rForwardStart := forward_init (backInput scanned count) copied
    have rForward := forward_run (backInput scanned count) [] copied
    let finish :=
      ({ forwardState (backInput scanned count) copied [] with
         pc := 29, halted := true } : Configuration)
    have rHalt : RunsFor program
        ({ forwardState (backInput scanned count) copied [] with pc := 29 } : Configuration)
        finish 1 := by
      exact RunsFor.succ (RunsFor.zero _) (halt_final _ _)
    have r1 : RunsFor program
        (headerState before 0 (List.replicate count true ++ false :: rest))
        (scanAnyState input count 0) (5 * count + 3) := by
      simpa [input, scanAnyState, headerFinish] using rHeader
    have r2 : RunsFor program (scanAnyState input count 0)
        ({ pc := 11, inputTape := scanned,
           outputTape := counterTape 0 count } : Configuration)
        (4 * count + 1) := by
      simpa [scanned, scanAnyState] using rScan
    have r3 : RunsFor program
        ({ pc := 11, inputTape := scanned,
           outputTape := counterTape 0 count } : Configuration)
        ({ pc := 16, inputTape := scanned,
           outputTape := copyTape count [] } : Configuration)
        (1 + (3 * count + 2)) := by
      simpa [seekState] using rSeekStart.trans rSeek
    have r4 : RunsFor program
        ({ pc := 16, inputTape := scanned,
           outputTape := copyTape count [] } : Configuration)
        (forwardState (backInput scanned count) [] copied)
        (copySteps + 1) := by
      have rCopy' : RunsFor program (copyState scanned count [])
          ({ pc := 24, inputTape := backInput scanned count,
             outputTape := copyTape 0 copied } : Configuration) copySteps := rCopy
      simpa [copyState] using rCopy'.trans rForwardStart
    have r5 : RunsFor program
        (forwardState (backInput scanned count) [] copied)
        finish ((4 * copied.length + 1) + 1) := by
      simpa [finish] using rForward.trans rHalt
    have run := ((((r1.trans r2).trans r3).trans r4).trans r5)
    refine ⟨finish,
      (5 * count + 3) + (4 * count + 1) + (1 + (3 * count + 2)) +
        (copySteps + 1) + ((4 * copied.length + 1) + 1), copied, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      simp only [List.length_nil, Nat.add_zero] at hCopied
      omega
    · simpa [headerState] using run
    · simpa [finish, forwardState, scanOutput] using
        Tape.Equivalent.refl ({ left := copied.reverse.map some ++ [none] } : Tape)
    · have hRestore : forwardInput (backInput scanned count) count = scanned := by
        have hSplit : scanned.left.take count ++ scanned.left.drop count = scanned.left :=
          List.take_append_drop count scanned.left
        have hTake : (scanned.left.take count).length = count := by
          simp [List.length_take, Nat.min_eq_left hLeft]
        simpa [hTake] using
          forward_back scanned (scanned.left.take count) (scanned.left.drop count)
            hSplit.symm
      obtain ⟨left, hSuffix⟩ := forwardInput_suffix
        (some false :: List.replicate count (some true) ++ before) rest count
      refine ⟨left, rest.drop count, ?_, ?_⟩
      · have hCopied' : copied.length = count := by simpa using hCopied
        have hInputEq : finish.inputTape = scanned := by
          change forwardInput (backInput scanned count) copied.length = scanned
          rw [hCopied', hRestore]
        rw [hInputEq]
        simpa [scanned, input, headerFinish] using hSuffix
      · simp only [List.length_drop, List.length_append, List.length_replicate,
          List.length_cons]
        omega

theorem runs_any_from (before : List (Option Bool)) (inputBits : List Bool) :
    ∃ finish used, used ≤ 23 * inputBits.length + 11 ∧
      RunsFor program
        { inputTape := { Tape.ofBits inputBits with left := before } }
        finish used ∧ finish.halted = true := by
  obtain ⟨finish, used, _, hUsed, run, hHalt, _, _⟩ :=
    runs_any_from_layout before inputBits
  exact ⟨finish, used, hUsed, run, hHalt⟩

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (23 * bits.length + 11) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ := runs_any_from [] bits
  have hInitial :
      ({ inputTape := { Tape.ofBits bits with left := [] } } : Configuration) =
        Configuration.initial bits := by cases bits <;> rfl
  rw [hInitial] at run
  have hNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ program := by
    simp [program]
  exact run.haltsFrom_of_no_randomBit hHalt hNoRandom hUsed

/-- The evaluator agrees with the finite transition trace on a valid frame. -/
theorem eval_valid (bits rest : List Bool) :
    evalWithin program (frame bits ++ rest)
      (23 * (frame bits ++ rest).length + 11) = PMF.pure (some bits) := by
  obtain ⟨target, used, hUsed, run, hHalt, _, _, hOutput⟩ :=
    runs_valid [] bits rest
  have hInitial :
      ({ inputTape := { Tape.ofBits (frame bits ++ rest) with left := [] } } :
        Configuration) = Configuration.initial (frame bits ++ rest) := by
    cases hBits : frame bits ++ rest <;>
      simp [Configuration.initial, Tape.ofBits]
  rw [hInitial] at run
  have hNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ program := by
    simp [program]
  have hBound : used ≤ 23 * (frame bits ++ rest).length + 11 := by
    simp only [frame, List.length_append, List.length_replicate,
      List.length_cons]
    omega
  have hAll := run.haltsFrom_of_no_randomBit hHalt hNoRandom
    (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit hNoRandom]
  simp [PMF.pure_map, hHalt, Configuration.outputBits, hOutput]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨fun length => 23 * length + 11, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 23).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 11)

/-- Every running transition stays inside the finite copier block. This
allows its trace to be embedded into a larger native program. -/
theorem control_closed (c d : Configuration)
    (hPc : c.pc < program.length) (step : Step program c d)
    (hRunning : d.halted = false) : d.pc < program.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 30 at hPc
  change d.pc < 30
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex,
    program, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine.FramePayloadCopy
