import Foundation.Machine.SecurityWidthTemplate
import Foundation.Machine.BitstringRewind
import Foundation.Machine.TapeSwap

namespace Machine.FrameWidthCheck

/-- Compare a unary frame header and its payload against a finite counter
already written on the output tape. The counter starts at its first cell.
Address 17 accepts a field of exactly the counter width; address 18 rejects
an early delimiter, an overlong header, or a truncated payload. The code
does not interpret the payload bits. -/
private def headCode : Program :=
  [.branch .input 18 5 1,
   .branch .output 18 2 2,
   .moveRight .input,
   .moveRight .output,
   .jump 0,
   .branch .output 6 18 18,
   .moveRight .input]

private def suffix : Program :=
  [.branch .output 17 13 13,
   .branch .input 18 14 14,
   .moveRight .input,
   .moveRight .output,
   .jump 12,
   .halt,
   .write .output true,
   .halt]

def program : Program :=
  headCode ++ rewindBitstring.swapTapes.asSubroutine 7 12 ++ suffix

private theorem program_eq :
    program = Program.withSubroutine headCode rewindBitstring.swapTapes suffix 12 := by
  rfl

theorem length : program.length = 20 := by decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private def counterTape : Nat → Nat → Tape
  | 0, passed =>
      { left := List.replicate passed (some false) }
  | remaining + 1, passed =>
      { left := List.replicate passed (some false), current := some false,
        right := List.replicate remaining (some false) ++ [none] }

private def headerState (before : List (Option Bool))
    (passed remaining : Nat) (payload rest : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits
      (List.replicate remaining true ++ false :: payload ++ rest) with
      left := List.replicate passed (some true) ++ before },
    outputTape := counterTape remaining passed }

private def headerScan (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with
      left := List.replicate passed (some true) ++ before },
    outputTape := counterTape remaining passed }

/-- Entry point for checking one framed field against a preloaded counter.
The counter is a contiguous block of `count` bit cells. -/
def start (before : List (Option Bool))
    (count : Nat) (bits : List Bool) : Configuration :=
  headerScan before 0 count bits

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> rfl
  | cons cell cells ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- A counter loaded as ordinary bits has the same cells as the checker's
entry counter. The checker retains one redundant outer blank physically. -/
theorem start_equivalent (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    (start before count bits).Equivalent
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate count false) } : Configuration) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact (Tape.Equivalent.refl _)
  · cases count with
    | zero => exact Tape.Equivalent.refl _
    | succ count =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        simpa [start, headerScan, counterTape, Tape.ofBits,
          List.replicate_succ] using
          getD_append_blank (List.replicate count (some false)) i

private theorem counterTape_moveRight (remaining passed : Nat) :
    (counterTape (remaining + 1) passed).moveRight =
      counterTape remaining (passed + 1) := by
  cases remaining <;>
    simp [counterTape, Tape.moveRight, List.replicate_succ]

private theorem header_one (before : List (Option Bool))
    (passed remaining : Nat) (payload rest : List Bool) :
    RunsFor program (headerState before passed (remaining + 1) payload rest)
      (headerState before (passed + 1) remaining payload rest) 5 := by
  let start := headerState before passed (remaining + 1) payload rest
  let selected : Configuration := { start with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let movedInput : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, headerState,
      Instruction.next, Configuration.tape, Tape.ofBits, List.replicate_succ]
  have hCheck : Step program selected checked := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
      headerState, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked movedInput := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
      headerState, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
      headerState, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (headerState before (passed + 1) remaining payload rest) := by
    cases remaining <;> cases payload <;>
      simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
        movedInput, movedOutput, headerState, counterTape,
        Instruction.next, Tape.moveRight, Tape.ofBits,
        List.replicate_succ, List.append_assoc]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hCheck) hInput) hOutput) hBack

private def headerFinish (before : List (Option Bool))
    (count : Nat) (payload rest : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { Tape.ofBits (payload ++ rest) with
      left := some false :: List.replicate count (some true) ++ before },
    outputTape := counterTape 0 count }

private theorem header_end (before : List (Option Bool))
    (count : Nat) (payload rest : List Bool) :
    RunsFor program (headerState before count 0 payload rest)
      (headerFinish before count payload rest) 3 := by
  let start := headerState before count 0 payload rest
  let selected : Configuration := { start with pc := 5 }
  let checked : Configuration := { selected with pc := 6 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, headerState,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected checked := by
    simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
      headerState, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked (headerFinish before count payload rest) := by
    cases payload <;> cases rest <;>
      simp [Step, successors, next, program, headCode, suffix, start, selected, checked,
        headerState, headerFinish, counterTape, Instruction.next,
        Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.ofBits]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hCheck) hInput

private theorem header_run (before : List (Option Bool))
    (passed remaining : Nat) (payload rest : List Bool) :
    RunsFor program (headerState before passed remaining payload rest)
      (headerFinish before (passed + remaining) payload rest)
      (5 * remaining + 3) := by
  induction remaining generalizing passed with
  | zero => simpa using header_end before passed payload rest
  | succ remaining ih =>
      have first := header_one before passed remaining payload rest
      have tail := ih (passed + 1)
      have hCount : passed + 1 + remaining = passed + (remaining + 1) := by omega
      rw [hCount] at tail
      convert first.trans tail using 1
      omega

private def checkTape : Nat → Nat → Tape
  | 0, passed =>
      { left := List.replicate passed (some false) ++ [none] }
  | remaining + 1, passed =>
      { left := List.replicate passed (some false) ++ [none],
        current := some false,
        right := List.replicate remaining (some false) ++ [none] }

private theorem checkTape_moveRight (remaining passed : Nat) :
    (checkTape (remaining + 1) passed).moveRight =
      checkTape remaining (passed + 1) := by
  cases remaining <;>
    simp [checkTape, Tape.moveRight, List.replicate_succ]

private def payloadState (before : List (Option Bool)) (count : Nat)
    (processed remaining rest : List Bool) : Configuration :=
  { pc := 12,
    inputTape := { Tape.ofBits (remaining ++ rest) with
      left := processed.reverse.map some ++
        some false :: List.replicate count (some true) ++ before },
    outputTape := checkTape remaining.length processed.length }

private theorem payload_one (before : List (Option Bool)) (count : Nat)
    (processed remaining rest : List Bool) (bit : Bool) :
    RunsFor program (payloadState before count processed (bit :: remaining) rest)
      (payloadState before count (processed ++ [bit]) remaining rest) 5 := by
  let start := payloadState before count processed (bit :: remaining) rest
  let selected : Configuration := { start with pc := 13 }
  let checked : Configuration := { selected with pc := 14 }
  let movedInput : Configuration :=
    { checked with pc := 15, inputTape := checked.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 16, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    have hLookup : program[12]? = some (.branch .output 17 13 13) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadState,
      checkTape, Instruction.next, Configuration.tape]
  have hCheck : Step program selected checked := by
    have hLookup : program[13]? = some (.branch .input 18 14 14) := by decide
    cases bit <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        payloadState, Instruction.next, Configuration.tape, Tape.ofBits]
  have hInput : Step program checked movedInput := by
    have hLookup : program[14]? = some (.moveRight .input) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadState, movedInput, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    have hLookup : program[15]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadState, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (payloadState before count (processed ++ [bit]) remaining rest) := by
    have hLookup : program[16]? = some (.jump 12) := by decide
    cases remaining <;> cases rest <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        movedInput, movedOutput, payloadState, checkTape,
        Instruction.next, Tape.moveRight, Tape.ofBits,
        List.reverse_append, List.append_assoc, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hCheck) hInput) hOutput) hBack

private theorem payload_end (before : List (Option Bool)) (count : Nat)
    (processed rest : List Bool) :
    RunsFor program (payloadState before count processed [] rest)
      { payloadState before count processed [] rest with pc := 17, halted := true } 2 := by
  let start := payloadState before count processed [] rest
  let selected : Configuration := { start with pc := 17 }
  have hBranch : Step program start selected := by
    have hLookup : program[12]? = some (.branch .output 17 13 13) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadState,
      checkTape, Instruction.next, Configuration.tape]
  have hHalt : Step program selected { selected with halted := true } := by
    have hLookup : program[17]? = some .halt := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadState,
      Instruction.next]
  exact (RunsFor.zero start).succ hBranch |>.succ hHalt

private theorem payload_run (before : List (Option Bool)) (count : Nat)
    (processed remaining rest : List Bool) :
    RunsFor program (payloadState before count processed remaining rest)
      { payloadState before count (processed ++ remaining) [] rest with
        pc := 17, halted := true }
      (5 * remaining.length + 2) := by
  induction remaining generalizing processed with
  | nil => simpa using payload_end before count processed rest
  | cons bit remaining ih =>
      have first := payload_one before count processed remaining rest bit
      have tail := ih (processed ++ [bit])
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using first.trans tail

/-- A frame with exactly the counter width is accepted after a linear number
of actual machine transitions. The next field remains unread on the input
tape; the counter remains on the output tape for the caller. -/
theorem runs_valid (before : List (Option Bool))
    (payload rest : List Bool) (count : Nat)
    (hLength : payload.length = count) :
    ∃ target used,
      used ≤ 12 * count + 9 ∧
      RunsFor program (start before count (frame payload ++ rest)) target used ∧
      target.halted = true ∧
      target.pc = 17 ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := payload.reverse.map some ++
            some false :: List.replicate count (some true) ++ before } ∧
      target.outputTape = checkTape 0 count := by
  let afterHeader := headerFinish before count payload rest
  have hHeader : RunsFor program (headerState before 0 count payload rest)
      afterHeader (5 * count + 3) := by
    simpa [afterHeader] using header_run before 0 count payload rest
  let input := afterHeader.inputTape
  let sourceStart := (rewindBitstringStart (List.replicate count false) input).swapTapes
  let sourceFinish := (rewindBitstringFinish (List.replicate count false) input).swapTapes
  have hStart : afterHeader = sourceStart.rebasePc headCode.length := by
    simp [afterHeader, sourceStart, input, headerFinish, counterTape,
      headCode, rewindBitstringStart, Configuration.swapTapes,
      Configuration.rebasePc]
  have hSource : RunsFor rewindBitstring.swapTapes sourceStart sourceFinish
      (2 * count + 4) := by
    simpa [sourceStart, sourceFinish] using
      (rewindBitstring_runs (List.replicate count false) input).swapTapes
  obtain ⟨u, hu, embedded⟩ := hSource.withSubroutine_halted
    headCode rewindBitstring.swapTapes suffix 12
    (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
    (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
    (by simp [sourceFinish, Configuration.swapTapes, rewindBitstringFinish])
  have hMiddle : RunsFor program afterHeader (sourceFinish.resumeAt 12) u := by
    rw [program_eq, hStart]
    exact embedded
  have hPayloadStart : sourceFinish.resumeAt 12 =
      payloadState before count [] payload rest := by
    cases count with
    | zero =>
        simp [sourceFinish, input, afterHeader, rewindBitstringFinish,
          headerFinish, checkTape, payloadState, counterTape,
          Configuration.swapTapes, Configuration.resumeAt, Tape.moveRight,
          Tape.ofBits, hLength]
    | succ count =>
        simp [sourceFinish, input, afterHeader, rewindBitstringFinish,
          headerFinish, checkTape, payloadState, counterTape,
          Configuration.swapTapes, Configuration.resumeAt, Tape.moveRight,
          Tape.ofBits, hLength, List.replicate_succ]
  have hPayload : RunsFor program (sourceFinish.resumeAt 12)
      { payloadState before count payload [] rest with pc := 17, halted := true }
      (5 * count + 2) := by
    rw [hPayloadStart]
    simpa [hLength] using payload_run before count [] payload rest
  have hEntry : start before count (frame payload ++ rest) =
      headerState before 0 count payload rest := by
    simp [start, headerScan, headerState, frame, hLength]
  refine ⟨{ payloadState before count payload [] rest with pc := 17, halted := true },
    (5 * count + 3) + u + (5 * count + 2), by omega,
    ?_, rfl, rfl, ?_, ?_⟩
  · rw [hEntry]
    exact (hHeader.trans hMiddle).trans hPayload
  · simp [payloadState, checkTape, Tape.ofBits]
  · simp [payloadState, checkTape, hLength]

private theorem header_one_any (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed (remaining + 1) (true :: bits))
      (headerScan before (passed + 1) remaining bits) 5 := by
  let start := headerScan before passed (remaining + 1) (true :: bits)
  let selected : Configuration := { start with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let movedInput : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      headerScan, Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected checked := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      checked, headerScan, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked movedInput := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      checked, headerScan, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      checked, headerScan, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (headerScan before (passed + 1) remaining bits) := by
    cases bits <;> cases remaining <;>
      simp [Step, successors, next, program, headCode, suffix, start,
        selected, checked, movedInput, movedOutput, headerScan, counterTape,
        Instruction.next, Tape.moveRight, Tape.ofBits,
        List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hCheck) hInput) hOutput) hBack

private theorem header_end_any (before : List (Option Bool))
    (passed : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed 0 (false :: bits))
      { pc := 7,
        inputTape := { Tape.ofBits bits with
          left := some false :: List.replicate passed (some true) ++ before },
        outputTape := counterTape 0 passed } 3 := by
  let start := headerScan before passed 0 (false :: bits)
  let selected : Configuration := { start with pc := 5 }
  let checked : Configuration := { selected with pc := 6 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      headerScan, Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected checked := by
    simp [Step, successors, next, program, headCode, suffix, start, selected,
      checked, headerScan, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked
      { pc := 7,
        inputTape := { Tape.ofBits bits with
          left := some false :: List.replicate passed (some true) ++ before },
        outputTape := counterTape 0 passed } := by
    cases bits <;>
      simp [Step, successors, next, program, headCode, suffix, start,
        selected, checked, headerScan, counterTape, Instruction.next,
        Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.ofBits]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hCheck) hInput

private def rejectFinish (c : Configuration) : Configuration :=
  { c with pc := 19, outputTape := c.outputTape.write (some true), halted := true }

private theorem reject_run (c : Configuration)
    (hPc : c.pc = 18) (hActive : c.halted = false) :
    RunsFor program c (rejectFinish c) 2 := by
  let marked : Configuration :=
    { c with pc := 19, outputTape := c.outputTape.write (some true) }
  have hWrite : Step program c marked := by
    have hLookup : program[18]? = some (.write .output true) := by decide
    simp [Step, successors, next, hPc, hActive, hLookup, marked,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program marked (rejectFinish c) := by
    have hLookup : program[19]? = some .halt := by decide
    simp [Step, successors, next, hLookup, marked, rejectFinish,
      hActive, Instruction.next]
  exact ((RunsFor.zero c).succ hWrite).succ hHalt

private theorem header_blank_any (before : List (Option Bool))
    (passed remaining : Nat) :
    RunsFor program (headerScan before passed remaining [])
      (rejectFinish { headerScan before passed remaining [] with pc := 18 }) 3 := by
  let start := headerScan before passed remaining []
  let rejected : Configuration := { start with pc := 18 }
  have hBranch : Step program start rejected := by
    have hLookup : program[0]? = some (.branch .input 18 5 1) := by decide
    simp [Step, successors, next, hLookup, start, rejected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  exact ((RunsFor.zero start).succ hBranch).trans
    (reject_run rejected rfl rfl)

private theorem header_false_short (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed (remaining + 1) (false :: bits))
      (rejectFinish { headerScan before passed (remaining + 1) (false :: bits) with
        pc := 18 }) 4 := by
  let start := headerScan before passed (remaining + 1) (false :: bits)
  let selected : Configuration := { start with pc := 5 }
  let rejected : Configuration := { start with pc := 18 }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 18 5 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected rejected := by
    have hLookup : program[5]? = some (.branch .output 6 18 18) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

private theorem header_true_long (before : List (Option Bool))
    (passed : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed 0 (true :: bits))
      (rejectFinish { headerScan before passed 0 (true :: bits) with
        pc := 18 }) 4 := by
  let start := headerScan before passed 0 (true :: bits)
  let selected : Configuration := { start with pc := 1 }
  let rejected : Configuration := { start with pc := 18 }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 18 5 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected rejected := by
    have hLookup : program[1]? = some (.branch .output 18 2 2) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

private def headerSuccess (before : List (Option Bool))
    (passed : Nat) (tail : List Bool) : Configuration :=
  { pc := 7,
    inputTape := { Tape.ofBits tail with
      left := some false :: List.replicate passed (some true) ++ before },
    outputTape := counterTape 0 passed }

/-- The header scan either rejects within the counter width or reaches the
rewind subroutine after consuming exactly that many unary `true` cells. -/
private theorem header_run_any (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    ∃ finish used,
      used ≤ 5 * remaining + 4 ∧
      RunsFor program (headerScan before passed remaining bits) finish used ∧
      ((finish.halted = true ∧ finish.pc = 19 ∧
          finish.outputTape.current = some true) ∨
        ∃ tail, bits = List.replicate remaining true ++ false :: tail ∧
          finish = headerSuccess before (passed + remaining) tail) := by
  induction remaining generalizing passed bits with
  | zero =>
      cases bits with
      | nil =>
          refine ⟨_, 3, by omega, header_blank_any before passed 0, Or.inl ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons bit tail =>
          cases bit with
          | false =>
              refine ⟨_, 3, by omega, header_end_any before passed tail,
                Or.inr ⟨tail, rfl, ?_⟩⟩
              simp [headerSuccess]
          | true =>
              refine ⟨_, 4, by omega, header_true_long before passed tail,
                Or.inl ?_⟩
              exact ⟨rfl, rfl, rfl⟩
  | succ remaining ih =>
      cases bits with
      | nil =>
          refine ⟨_, 3, by omega, header_blank_any before passed (remaining + 1),
            Or.inl ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons bit tail =>
          cases bit with
          | false =>
              refine ⟨_, 4, by omega,
                header_false_short before passed remaining tail, Or.inl ?_⟩
              exact ⟨rfl, rfl, rfl⟩
          | true =>
              obtain ⟨finish, used, hUsed, run, outcome⟩ := ih (passed + 1) tail
              refine ⟨finish, 5 + used, by omega,
                (header_one_any before passed remaining tail).trans run, ?_⟩
              rcases outcome with reject | ⟨suffixBits, hBits, hFinish⟩
              · exact Or.inl reject
              · refine Or.inr ⟨suffixBits, ?_, ?_⟩
                · simp [hBits, List.replicate_succ]
                · rw [hFinish]
                  congr 1
                  omega

private def payloadScan (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bits : List Bool) : Configuration :=
  { pc := 12,
    inputTape := { Tape.ofBits bits with
      left := processed.reverse.map some ++
        some false :: List.replicate count (some true) ++ before },
    outputTape := checkTape remaining processed.length }

private theorem payload_one_any (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bit : Bool) (bits : List Bool) :
    RunsFor program (payloadScan before count processed (remaining + 1) (bit :: bits))
      (payloadScan before count (processed ++ [bit]) remaining bits) 5 := by
  let start := payloadScan before count processed (remaining + 1) (bit :: bits)
  let selected : Configuration := { start with pc := 13 }
  let checked : Configuration := { selected with pc := 14 }
  let movedInput : Configuration :=
    { checked with pc := 15, inputTape := checked.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 16, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step program start selected := by
    have hLookup : program[12]? = some (.branch .output 17 13 13) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hCheck : Step program selected checked := by
    have hLookup : program[13]? = some (.branch .input 18 14 14) := by decide
    cases bit <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        payloadScan, Instruction.next, Configuration.tape, Tape.ofBits]
  have hInput : Step program checked movedInput := by
    have hLookup : program[14]? = some (.moveRight .input) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    have hLookup : program[15]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput
      (payloadScan before count (processed ++ [bit]) remaining bits) := by
    have hLookup : program[16]? = some (.jump 12) := by decide
    cases remaining <;> cases bits <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        movedInput, movedOutput, payloadScan, checkTape,
        Instruction.next, Tape.moveRight, Tape.ofBits,
        List.reverse_append, List.append_assoc, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hCheck) hInput) hOutput) hBack

private theorem payload_end_any (before : List (Option Bool)) (count : Nat)
    (processed bits : List Bool) :
    RunsFor program (payloadScan before count processed 0 bits)
      { payloadScan before count processed 0 bits with pc := 17, halted := true } 2 := by
  let start := payloadScan before count processed 0 bits
  let selected : Configuration := { start with pc := 17 }
  have hBranch : Step program start selected := by
    have hLookup : program[12]? = some (.branch .output 17 13 13) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hHalt : Step program selected { selected with halted := true } := by
    have hLookup : program[17]? = some .halt := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      Instruction.next]
  exact ((RunsFor.zero start).succ hBranch).succ hHalt

private theorem payload_blank_any (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) :
    RunsFor program (payloadScan before count processed (remaining + 1) [])
      (rejectFinish { payloadScan before count processed (remaining + 1) [] with
        pc := 18 }) 4 := by
  let start := payloadScan before count processed (remaining + 1) []
  let selected : Configuration := { start with pc := 13 }
  let rejected : Configuration := { start with pc := 18 }
  have hBranch : Step program start selected := by
    have hLookup : program[12]? = some (.branch .output 17 13 13) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hCheck : Step program selected rejected := by
    have hLookup : program[13]? = some (.branch .input 18 14 14) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      payloadScan, Instruction.next, Configuration.tape, Tape.ofBits]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

/-- The payload scan rejects a truncated field; otherwise it consumes exactly
the number of counter cells and leaves the remaining suffix unread. -/
private theorem payload_run_any (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bits : List Bool) :
    ∃ finish used,
      used ≤ 5 * remaining + 4 ∧
      RunsFor program (payloadScan before count processed remaining bits)
        finish used ∧
      ((finish.halted = true ∧ finish.pc = 19 ∧
          finish.outputTape.current = some true) ∨
        ∃ consumed tail,
          bits = consumed ++ tail ∧ consumed.length = remaining ∧
          finish =
            { payloadScan before count (processed ++ consumed) 0 tail with
              pc := 17, halted := true }) := by
  induction remaining generalizing processed bits with
  | zero =>
      refine ⟨_, 2, by omega, payload_end_any before count processed bits,
        Or.inr ⟨[], bits, rfl, rfl, ?_⟩⟩
      simp
  | succ remaining ih =>
      cases bits with
      | nil =>
          refine ⟨_, 4, by omega,
            payload_blank_any before count processed remaining, Or.inl ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons bit bits =>
          obtain ⟨finish, used, hUsed, run, outcome⟩ :=
            ih (processed ++ [bit]) bits
          refine ⟨finish, 5 + used, by omega,
            (payload_one_any before count processed remaining bit bits).trans run,
            ?_⟩
          rcases outcome with rejected | ⟨consumed, tail, hBits, hLen, hFinish⟩
          · exact Or.inl rejected
          · refine Or.inr ⟨bit :: consumed, tail, ?_, ?_, ?_⟩
            · simp [hBits]
            · simp [hLen]
            · simpa [List.append_assoc] using hFinish

/-- From a finite counter and a contiguous finite input suffix, the complete
frame-width checker halts in linear time. Acceptance certifies that the raw
suffix starts with a frame whose payload has exactly the counter width. -/
theorem runs_any (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    ∃ target used,
      used ≤ 12 * count + 12 ∧
      RunsFor program (start before count bits) target used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 17 then none else some true) ∧
      (target.pc = 17 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape =
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape =
            { left := List.replicate count (some false) ++ [none] }) := by
  obtain ⟨afterHeader, hSteps, hhSteps, hHeader, hOutcome⟩ :=
    header_run_any before 0 count bits
  rcases hOutcome with hRejected | ⟨tail, hBits, hAfterHeader⟩
  · refine ⟨afterHeader, hSteps, by omega, hHeader, hRejected.1, ?_, ?_⟩
    · simpa [hRejected.2.1] using hRejected.2.2
    intro hAccept
    omega
  · subst afterHeader
    have hHeader' : RunsFor program (headerScan before 0 count bits)
        (headerSuccess before count tail) hSteps := by
      simpa using hHeader
    let input := (headerSuccess before count tail).inputTape
    let sourceStart :=
      (rewindBitstringStart (List.replicate count false) input).swapTapes
    let sourceFinish :=
      (rewindBitstringFinish (List.replicate count false) input).swapTapes
    have hStart : headerSuccess before count tail =
        sourceStart.rebasePc headCode.length := by
      simp [headerSuccess, sourceStart, input, counterTape, headCode,
        rewindBitstringStart, Configuration.swapTapes,
        Configuration.rebasePc]
    have hSource : RunsFor rewindBitstring.swapTapes sourceStart sourceFinish
        (2 * count + 4) := by
      simpa [sourceStart, sourceFinish] using
        (rewindBitstring_runs (List.replicate count false) input).swapTapes
    obtain ⟨rewindSteps, hRewindSteps, embedded⟩ :=
      hSource.withSubroutine_halted
        headCode rewindBitstring.swapTapes suffix 12
        (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
        (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
        (by simp [sourceFinish, Configuration.swapTapes, rewindBitstringFinish])
    have hMiddle : RunsFor program (headerSuccess before count tail)
        (sourceFinish.resumeAt 12) rewindSteps := by
      rw [program_eq, hStart]
      exact embedded
    have hPayloadStart : sourceFinish.resumeAt 12 =
        payloadScan before count [] count tail := by
      cases count with
      | zero =>
          simp [sourceFinish, input, headerSuccess, rewindBitstringFinish,
            checkTape, payloadScan, counterTape, Configuration.swapTapes,
            Configuration.resumeAt, Tape.moveRight, Tape.ofBits]
      | succ count =>
          simp [sourceFinish, input, headerSuccess, rewindBitstringFinish,
            checkTape, payloadScan, counterTape, Configuration.swapTapes,
            Configuration.resumeAt, Tape.moveRight, Tape.ofBits,
            List.replicate_succ]
    obtain ⟨target, payloadSteps, hPayloadSteps, hPayload, hPayloadOutcome⟩ :=
      payload_run_any before count [] count tail
    have hPayloadRun : RunsFor program (sourceFinish.resumeAt 12)
        target payloadSteps := by
      rw [hPayloadStart]
      exact hPayload
    have hRun : RunsFor program (headerScan before 0 count bits)
        target (hSteps + rewindSteps + payloadSteps) :=
      (hHeader'.trans hMiddle).trans hPayloadRun
    rcases hPayloadOutcome with hRejected | ⟨payload, rest, hTail, hLen, hTarget⟩
    · refine ⟨target, hSteps + rewindSteps + payloadSteps, by omega,
        hRun, hRejected.1, ?_, ?_⟩
      · simpa [hRejected.2.1] using hRejected.2.2
      intro hAccept
      omega
    · refine ⟨target, hSteps + rewindSteps + payloadSteps, by omega,
        hRun, ?_, ?_, ?_⟩
      · simp [hTarget]
      · simp [hTarget, payloadScan, checkTape]
      · intro _
        refine ⟨payload, rest, ?_, hLen, ?_, ?_⟩
        · simp [hBits, hTail, frame, hLen, List.append_assoc]
        · simp [hTarget, payloadScan]
        · simp [hTarget, payloadScan, checkTape, hLen]

/-- The checker can be called on the ordinary physical bitstring layout of
the counter, with no reset of either machine tape. -/
theorem runs_any_loaded (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    ∃ target used,
      used ≤ 12 * count + 12 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := before },
           outputTape := Tape.ofBits (List.replicate count false) } : Configuration)
        target used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 17 then none else some true) ∧
      (target.pc = 17 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate count (some false) ++ [none] }) := by
  obtain ⟨canonical, used, hUsed, run, hHalted, hStatus, hAccepted⟩ :=
    runs_any before count bits
  obtain ⟨actual, actualRun, hEquivalent⟩ :=
    run.exists_equivalent (start_equivalent before count bits)
  refine ⟨actual, used, hUsed, actualRun,
    hEquivalent.2.1.symm.trans hHalted, ?_, ?_⟩
  · simpa [hEquivalent.1] using hEquivalent.2.2.2.1.symm.trans hStatus
  intro hPc
  obtain ⟨payload, rest, hBits, hLength, hInput, hOutput⟩ :=
    hAccepted (hEquivalent.1.trans hPc)
  exact ⟨payload, rest, hBits, hLength,
    hEquivalent.2.2.1.symm.trans (by rw [hInput]; exact Tape.Equivalent.refl _),
    hEquivalent.2.2.2.symm.trans (by rw [hOutput]; exact Tape.Equivalent.refl _)⟩

/-- A valid frame cannot take the marked rejection branch. This applies to
any halted run from the loaded tapes, independently of its step count. -/
theorem accepts_valid_loaded (before : List (Option Bool))
    (payload rest : List Bool) (count : Nat)
    (hLength : payload.length = count)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      ({ inputTape := { Tape.ofBits (frame payload ++ rest) with left := before },
         outputTape := Tape.ofBits (List.replicate count false) } : Configuration)
      target used)
    (hHalt : target.halted = true) : target.pc = 17 := by
  obtain ⟨valid, validSteps, _, validRun, validHalt, validPc, _, _⟩ :=
    runs_valid before payload rest count hLength
  obtain ⟨loaded, loadedRun, hEquivalent⟩ :=
    validRun.exists_equivalent
      (start_equivalent before count (frame payload ++ rest))
  have hLoadedHalt : loaded.halted = true :=
    hEquivalent.2.1.symm.trans validHalt
  have hSame := loadedRun.halted_finish_eq_of_no_randomBit
    run hLoadedHalt hHalt no_randomBit
  exact hSame ▸ hEquivalent.1.symm.trans validPc

/-- Since the checker contains no random instruction, its concrete trace
implies the same polynomial stopping bound for every evaluator branch. -/
theorem haltsFrom (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (finish : Configuration)
    (run : PaddedRunsFor program (start before count bits) finish
      (12 * count + 12)) : finish.halted = true := by
  obtain ⟨target, used, hUsed, trace, hHalted, _, _⟩ := runs_any before count bits
  exact trace.haltsFrom_of_no_randomBit hHalted no_randomBit hUsed finish run

theorem haltsFrom_loaded (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (finish : Configuration)
    (run : PaddedRunsFor program
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate count false) } : Configuration)
      finish (12 * count + 12)) : finish.halted = true := by
  obtain ⟨target, used, hUsed, trace, hHalted, _, _⟩ :=
    runs_any_loaded before count bits
  exact trace.haltsFrom_of_no_randomBit hHalted no_randomBit hUsed finish run

end Machine.FrameWidthCheck
