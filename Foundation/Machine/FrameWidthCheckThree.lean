import Foundation.Machine.FrameWidthCheck

namespace Machine.FrameWidthCheckThree

/-- A fixed-width frame checker whose counter has three physical cells per
logical bit. The code advances the output head three times for each unary
header bit and each payload bit. It does not inspect the payload values. -/
private def headCode : Program :=
  [.branch .input 22 7 1,
   .branch .output 22 2 2,
   .moveRight .input,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .jump 0,
   .branch .output 8 22 22,
   .moveRight .input]

private def suffix : Program :=
  [.branch .output 21 15 15,
   .branch .input 22 16 16,
   .moveRight .input,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .jump 14,
   .halt,
   .write .output true,
   .halt]

def program : Program :=
  headCode ++ rewindBitstring.swapTapes.asSubroutine 9 14 ++ suffix

private theorem program_eq :
    program = Program.withSubroutine headCode rewindBitstring.swapTapes suffix 14 := by
  rfl

theorem length : program.length = 24 := by decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private def counterTape : Nat → Nat → Tape
  | 0, passed => { left := List.replicate (3 * passed) (some false) }
  | remaining + 1, passed =>
      { left := List.replicate (3 * passed) (some false),
        current := some false,
        right := List.replicate (3 * remaining + 2) (some false) ++ [none] }

private def headerScan (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with
      left := List.replicate passed (some true) ++ before },
    outputTape := counterTape remaining passed }

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

theorem start_equivalent (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    (start before count bits).Equivalent
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate (3 * count) false) } : Configuration) := by
  refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
  cases count with
  | zero => exact Tape.Equivalent.refl _
  | succ count =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simpa [start, headerScan, counterTape, Tape.ofBits,
        List.replicate_succ, Nat.mul_succ, List.replicate_add] using
        getD_append_blank (List.replicate (3 * count + 2) (some false)) i

private theorem counterTape_moveRight_three (remaining passed : Nat) :
    (((counterTape (remaining + 1) passed).moveRight).moveRight).moveRight =
      counterTape remaining (passed + 1) := by
  cases remaining with
  | zero =>
      simp [counterTape, Tape.moveRight, List.replicate_succ, Nat.mul_add]
  | succ remaining =>
      simp [counterTape, Tape.moveRight, List.replicate_succ, Nat.mul_add]

private theorem header_one (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed (remaining + 1) (true :: bits))
      (headerScan before (passed + 1) remaining bits) 7 := by
  let start := headerScan before passed (remaining + 1) (true :: bits)
  let selected : Configuration := { start with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let movedInput : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let movedOutput₁ : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  let movedOutput₂ : Configuration :=
    { movedOutput₁ with pc := 5, outputTape := movedOutput₁.outputTape.moveRight }
  let movedOutput₃ : Configuration :=
    { movedOutput₂ with pc := 6, outputTape := movedOutput₂.outputTape.moveRight }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 22 7 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected checked := by
    have hLookup : program[1]? = some (.branch .output 22 2 2) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked movedInput := by
    have hLookup : program[2]? = some (.moveRight .input) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₁ : Step program movedInput movedOutput₁ := by
    have hLookup : program[3]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, movedInput, movedOutput₁, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₂ : Step program movedOutput₁ movedOutput₂ := by
    have hLookup : program[4]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, movedInput, movedOutput₁, movedOutput₂, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₃ : Step program movedOutput₂ movedOutput₃ := by
    have hLookup : program[5]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, movedInput, movedOutput₁, movedOutput₂, movedOutput₃,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput₃
      (headerScan before (passed + 1) remaining bits) := by
    have hLookup : program[6]? = some (.jump 0) := by decide
    cases bits <;> cases remaining <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        movedInput, movedOutput₁, movedOutput₂, movedOutput₃,
        headerScan, counterTape, Instruction.next, Tape.moveRight,
        Tape.ofBits, List.replicate_succ, Nat.mul_add]
  have run1 := (RunsFor.zero start).succ hBranch
  have run2 := run1.succ hCheck
  have run3 := run2.succ hInput
  have run4 := run3.succ hOutput₁
  have run5 := run4.succ hOutput₂
  have run6 := run5.succ hOutput₃
  exact run6.succ hBack

private def headerSuccess (before : List (Option Bool))
    (passed : Nat) (tail : List Bool) : Configuration :=
  { pc := 9,
    inputTape := { Tape.ofBits tail with
      left := some false :: List.replicate passed (some true) ++ before },
    outputTape := counterTape 0 passed }

private theorem header_end (before : List (Option Bool))
    (passed : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed 0 (false :: bits))
      (headerSuccess before passed bits) 3 := by
  let start := headerScan before passed 0 (false :: bits)
  let selected : Configuration := { start with pc := 7 }
  let checked : Configuration := { selected with pc := 8 }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 22 7 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected checked := by
    have hLookup : program[7]? = some (.branch .output 8 22 22) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  have hInput : Step program checked (headerSuccess before passed bits) := by
    have hLookup : program[8]? = some (.moveRight .input) := by decide
    cases bits <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        headerScan, headerSuccess, counterTape, Instruction.next,
        Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.ofBits]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).succ hInput

private def rejectFinish (c : Configuration) : Configuration :=
  { c with pc := 23, outputTape := c.outputTape.write (some true), halted := true }

private theorem reject_run (c : Configuration)
    (hPc : c.pc = 22) (hActive : c.halted = false) :
    RunsFor program c (rejectFinish c) 2 := by
  let marked : Configuration :=
    { c with pc := 23, outputTape := c.outputTape.write (some true) }
  have hWrite : Step program c marked := by
    have hLookup : program[22]? = some (.write .output true) := by decide
    simp [Step, successors, next, hPc, hActive, hLookup, marked,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program marked (rejectFinish c) := by
    have hLookup : program[23]? = some .halt := by decide
    simp [Step, successors, next, hLookup, marked, rejectFinish,
      hActive, Instruction.next]
  exact ((RunsFor.zero c).succ hWrite).succ hHalt

private theorem header_blank (before : List (Option Bool))
    (passed remaining : Nat) :
    RunsFor program (headerScan before passed remaining [])
      (rejectFinish { headerScan before passed remaining [] with pc := 22 }) 3 := by
  let start := headerScan before passed remaining []
  let rejected : Configuration := { start with pc := 22 }
  have hBranch : Step program start rejected := by
    have hLookup : program[0]? = some (.branch .input 22 7 1) := by decide
    simp [Step, successors, next, hLookup, start, rejected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  exact ((RunsFor.zero start).succ hBranch).trans
    (reject_run rejected rfl rfl)

private theorem header_false_short (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed (remaining + 1) (false :: bits))
      (rejectFinish { headerScan before passed (remaining + 1) (false :: bits) with
        pc := 22 }) 4 := by
  let start := headerScan before passed (remaining + 1) (false :: bits)
  let selected : Configuration := { start with pc := 7 }
  let rejected : Configuration := { start with pc := 22 }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 22 7 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected rejected := by
    have hLookup : program[7]? = some (.branch .output 8 22 22) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

private theorem header_true_long (before : List (Option Bool))
    (passed : Nat) (bits : List Bool) :
    RunsFor program (headerScan before passed 0 (true :: bits))
      (rejectFinish { headerScan before passed 0 (true :: bits) with
        pc := 22 }) 4 := by
  let start := headerScan before passed 0 (true :: bits)
  let selected : Configuration := { start with pc := 1 }
  let rejected : Configuration := { start with pc := 22 }
  have hBranch : Step program start selected := by
    have hLookup : program[0]? = some (.branch .input 22 7 1) := by decide
    simp [Step, successors, next, hLookup, start, selected, headerScan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hCheck : Step program selected rejected := by
    have hLookup : program[1]? = some (.branch .output 22 2 2) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      headerScan, counterTape, Instruction.next, Configuration.tape]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

private theorem header_run_any (before : List (Option Bool))
    (passed remaining : Nat) (bits : List Bool) :
    ∃ finish used,
      used ≤ 7 * remaining + 4 ∧
      RunsFor program (headerScan before passed remaining bits) finish used ∧
      ((finish.halted = true ∧ finish.pc = 23 ∧
          finish.outputTape.current = some true) ∨
        ∃ tail, bits = List.replicate remaining true ++ false :: tail ∧
          finish = headerSuccess before (passed + remaining) tail) := by
  induction remaining generalizing passed bits with
  | zero =>
      cases bits with
      | nil =>
          refine ⟨_, 3, by omega, header_blank before passed 0, Or.inl ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons bit tail =>
          cases bit with
          | false =>
              refine ⟨_, 3, by omega, header_end before passed tail,
                Or.inr ⟨tail, rfl, ?_⟩⟩
              simp [headerSuccess]
          | true =>
              refine ⟨_, 4, by omega, header_true_long before passed tail,
                Or.inl ?_⟩
              exact ⟨rfl, rfl, rfl⟩
  | succ remaining ih =>
      cases bits with
      | nil =>
          refine ⟨_, 3, by omega, header_blank before passed (remaining + 1),
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
              refine ⟨finish, 7 + used, by omega,
                (header_one before passed remaining tail).trans run, ?_⟩
              rcases outcome with rejected | ⟨suffixBits, hBits, hFinish⟩
              · exact Or.inl rejected
              · refine Or.inr ⟨suffixBits, ?_, ?_⟩
                · simp [hBits, List.replicate_succ]
                · rw [hFinish]
                  congr 1
                  omega

private def checkTape : Nat → Nat → Tape
  | 0, passed =>
      { left := List.replicate (3 * passed) (some false) ++ [none] }
  | remaining + 1, passed =>
      { left := List.replicate (3 * passed) (some false) ++ [none],
        current := some false,
        right := List.replicate (3 * remaining + 2) (some false) ++ [none] }

private def payloadScan (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bits : List Bool) : Configuration :=
  { pc := 14,
    inputTape := { Tape.ofBits bits with
      left := processed.reverse.map some ++
        some false :: List.replicate count (some true) ++ before },
    outputTape := checkTape remaining processed.length }

private theorem payload_one (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bit : Bool) (bits : List Bool) :
    RunsFor program (payloadScan before count processed (remaining + 1) (bit :: bits))
      (payloadScan before count (processed ++ [bit]) remaining bits) 7 := by
  let start := payloadScan before count processed (remaining + 1) (bit :: bits)
  let selected : Configuration := { start with pc := 15 }
  let checked : Configuration := { selected with pc := 16 }
  let movedInput : Configuration :=
    { checked with pc := 17, inputTape := checked.inputTape.moveRight }
  let movedOutput₁ : Configuration :=
    { movedInput with pc := 18, outputTape := movedInput.outputTape.moveRight }
  let movedOutput₂ : Configuration :=
    { movedOutput₁ with pc := 19, outputTape := movedOutput₁.outputTape.moveRight }
  let movedOutput₃ : Configuration :=
    { movedOutput₂ with pc := 20, outputTape := movedOutput₂.outputTape.moveRight }
  have hBranch : Step program start selected := by
    have hLookup : program[14]? = some (.branch .output 21 15 15) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hCheck : Step program selected checked := by
    have hLookup : program[15]? = some (.branch .input 22 16 16) := by decide
    cases bit <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        payloadScan, Instruction.next, Configuration.tape, Tape.ofBits]
  have hInput : Step program checked movedInput := by
    have hLookup : program[16]? = some (.moveRight .input) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₁ : Step program movedInput movedOutput₁ := by
    have hLookup : program[17]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, movedOutput₁, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₂ : Step program movedOutput₁ movedOutput₂ := by
    have hLookup : program[18]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, movedOutput₁, movedOutput₂, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput₃ : Step program movedOutput₂ movedOutput₃ := by
    have hLookup : program[19]? = some (.moveRight .output) := by decide
    simp [Step, successors, next, hLookup, start, selected, checked,
      payloadScan, movedInput, movedOutput₁, movedOutput₂, movedOutput₃,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hBack : Step program movedOutput₃
      (payloadScan before count (processed ++ [bit]) remaining bits) := by
    have hLookup : program[20]? = some (.jump 14) := by decide
    cases bits <;> cases remaining <;>
      simp [Step, successors, next, hLookup, start, selected, checked,
        movedInput, movedOutput₁, movedOutput₂, movedOutput₃,
        payloadScan, checkTape, Instruction.next, Tape.moveRight,
        Tape.ofBits, List.reverse_append, List.replicate_succ,
        Nat.mul_add, List.append_assoc]
  have run1 := (RunsFor.zero start).succ hBranch
  have run2 := run1.succ hCheck
  have run3 := run2.succ hInput
  have run4 := run3.succ hOutput₁
  have run5 := run4.succ hOutput₂
  have run6 := run5.succ hOutput₃
  exact run6.succ hBack

private theorem payload_end (before : List (Option Bool)) (count : Nat)
    (processed bits : List Bool) :
    RunsFor program (payloadScan before count processed 0 bits)
      { payloadScan before count processed 0 bits with pc := 21, halted := true } 2 := by
  let start := payloadScan before count processed 0 bits
  let selected : Configuration := { start with pc := 21 }
  have hBranch : Step program start selected := by
    have hLookup : program[14]? = some (.branch .output 21 15 15) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hHalt : Step program selected { selected with halted := true } := by
    have hLookup : program[21]? = some .halt := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      Instruction.next]
  exact ((RunsFor.zero start).succ hBranch).succ hHalt

private theorem payload_blank (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) :
    RunsFor program (payloadScan before count processed (remaining + 1) [])
      (rejectFinish { payloadScan before count processed (remaining + 1) [] with
        pc := 22 }) 4 := by
  let start := payloadScan before count processed (remaining + 1) []
  let selected : Configuration := { start with pc := 15 }
  let rejected : Configuration := { start with pc := 22 }
  have hBranch : Step program start selected := by
    have hLookup : program[14]? = some (.branch .output 21 15 15) := by decide
    simp [Step, successors, next, hLookup, start, selected, payloadScan,
      checkTape, Instruction.next, Configuration.tape]
  have hCheck : Step program selected rejected := by
    have hLookup : program[15]? = some (.branch .input 22 16 16) := by decide
    simp [Step, successors, next, hLookup, start, selected, rejected,
      payloadScan, Instruction.next, Configuration.tape, Tape.ofBits]
  exact (((RunsFor.zero start).succ hBranch).succ hCheck).trans
    (reject_run rejected rfl rfl)

private theorem payload_run_any (before : List (Option Bool)) (count : Nat)
    (processed : List Bool) (remaining : Nat) (bits : List Bool) :
    ∃ finish used,
      used ≤ 7 * remaining + 4 ∧
      RunsFor program (payloadScan before count processed remaining bits)
        finish used ∧
      ((finish.halted = true ∧ finish.pc = 23 ∧
          finish.outputTape.current = some true) ∨
        ∃ consumed tail,
          bits = consumed ++ tail ∧ consumed.length = remaining ∧
          finish =
            { payloadScan before count (processed ++ consumed) 0 tail with
              pc := 21, halted := true }) := by
  induction remaining generalizing processed bits with
  | zero =>
      refine ⟨_, 2, by omega, payload_end before count processed bits,
        Or.inr ⟨[], bits, rfl, rfl, ?_⟩⟩
      simp
  | succ remaining ih =>
      cases bits with
      | nil =>
          refine ⟨_, 4, by omega,
            payload_blank before count processed remaining, Or.inl ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons bit bits =>
          obtain ⟨finish, used, hUsed, run, outcome⟩ :=
            ih (processed ++ [bit]) bits
          refine ⟨finish, 7 + used, by omega,
            (payload_one before count processed remaining bit bits).trans run,
            ?_⟩
          rcases outcome with rejected | ⟨consumed, tail, hBits, hLen, hFinish⟩
          · exact Or.inl rejected
          · refine Or.inr ⟨bit :: consumed, tail, ?_, ?_, ?_⟩
            · simp [hBits]
            · simp [hLen]
            · simpa [List.append_assoc] using hFinish

private theorem header_run_valid (before : List (Option Bool))
    (passed remaining : Nat) (tail : List Bool) :
    RunsFor program
      (headerScan before passed remaining
        (List.replicate remaining true ++ false :: tail))
      (headerSuccess before (passed + remaining) tail)
      (7 * remaining + 3) := by
  induction remaining generalizing passed with
  | zero => simpa using header_end before passed tail
  | succ remaining ih =>
      have first := header_one before passed remaining
        (List.replicate remaining true ++ false :: tail)
      have rest := ih (passed + 1)
      have hCount : passed + 1 + remaining = passed + (remaining + 1) := by omega
      rw [hCount] at rest
      convert first.trans rest using 1
      · simp [List.replicate_succ]
      · omega

private theorem payload_run_valid (before : List (Option Bool))
    (count : Nat) (processed payload rest : List Bool) :
    RunsFor program
      (payloadScan before count processed payload.length (payload ++ rest))
      { payloadScan before count (processed ++ payload) 0 rest with
        pc := 21, halted := true }
      (7 * payload.length + 2) := by
  induction payload generalizing processed with
  | nil => simpa using payload_end before count processed rest
  | cons bit payload ih =>
      have first := payload_one before count processed payload.length bit
        (payload ++ rest)
      have tail := ih (processed ++ [bit])
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using first.trans tail

/-- Every finite suffix halts against a three-cell-per-bit counter. Reaching
address 21 certifies a frame whose payload has one bit per counter triple. -/
theorem runs_any (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    ∃ target used,
      used ≤ 20 * count + 12 ∧
      RunsFor program (start before count bits) target used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 21 then none else some true) ∧
      (target.pc = 21 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape =
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape =
            { left := List.replicate (3 * count) (some false) ++ [none] }) := by
  obtain ⟨afterHeader, headerSteps, hHeaderSteps, hHeader, hOutcome⟩ :=
    header_run_any before 0 count bits
  rcases hOutcome with hRejected | ⟨tail, hBits, hAfterHeader⟩
  · refine ⟨afterHeader, headerSteps, by omega, hHeader, hRejected.1, ?_, ?_⟩
    · simpa [hRejected.2.1] using hRejected.2.2
    intro hAccept
    omega
  · subst afterHeader
    have hHeader' : RunsFor program (start before count bits)
        (headerSuccess before count tail) headerSteps := by
      simpa [start] using hHeader
    let input := (headerSuccess before count tail).inputTape
    let sourceStart :=
      (rewindBitstringStart (List.replicate (3 * count) false) input).swapTapes
    let sourceFinish :=
      (rewindBitstringFinish (List.replicate (3 * count) false) input).swapTapes
    have hStart : headerSuccess before count tail =
        sourceStart.rebasePc headCode.length := by
      simp [headerSuccess, sourceStart, input, counterTape, headCode,
        rewindBitstringStart, Configuration.swapTapes,
        Configuration.rebasePc]
    have hSource : RunsFor rewindBitstring.swapTapes sourceStart sourceFinish
        (2 * (3 * count) + 4) := by
      simpa [sourceStart, sourceFinish] using
        (rewindBitstring_runs (List.replicate (3 * count) false) input).swapTapes
    obtain ⟨rewindSteps, hRewindSteps, embedded⟩ :=
      hSource.withSubroutine_halted
        headCode rewindBitstring.swapTapes suffix 14
        (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
        (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
        (by simp [sourceFinish, Configuration.swapTapes, rewindBitstringFinish])
    have hMiddle : RunsFor program (headerSuccess before count tail)
        (sourceFinish.resumeAt 14) rewindSteps := by
      rw [program_eq, hStart]
      exact embedded
    have hPayloadStart : sourceFinish.resumeAt 14 =
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
            List.replicate_succ, Nat.mul_succ]
    obtain ⟨target, payloadSteps, hPayloadSteps, hPayload, hPayloadOutcome⟩ :=
      payload_run_any before count [] count tail
    have hPayloadRun : RunsFor program (sourceFinish.resumeAt 14)
        target payloadSteps := by
      rw [hPayloadStart]
      exact hPayload
    have hRun : RunsFor program (start before count bits)
        target (headerSteps + rewindSteps + payloadSteps) :=
      (hHeader'.trans hMiddle).trans hPayloadRun
    rcases hPayloadOutcome with hRejected | ⟨payload, rest, hTail, hLen, hTarget⟩
    · refine ⟨target, headerSteps + rewindSteps + payloadSteps, by omega,
        hRun, hRejected.1, ?_, ?_⟩
      · simpa [hRejected.2.1] using hRejected.2.2
      intro hAccept
      omega
    · refine ⟨target, headerSteps + rewindSteps + payloadSteps, by omega,
        hRun, ?_, ?_, ?_⟩
      · simp [hTarget]
      · simp [hTarget, payloadScan, checkTape]
      · intro _
        refine ⟨payload, rest, ?_, hLen, ?_, ?_⟩
        · simp [hBits, hTail, frame, hLen, List.append_assoc]
        · simp [hTarget, payloadScan]
        · simp [hTarget, payloadScan, checkTape, hLen]

/-- A correctly framed field is accepted by the three-cell counter checker.
The result includes the actual next input-head position. -/
theorem runs_valid (before : List (Option Bool))
    (payload rest : List Bool) (count : Nat)
    (hLength : payload.length = count) :
    ∃ target used,
      used ≤ 20 * count + 9 ∧
      RunsFor program (start before count (frame payload ++ rest)) target used ∧
      target.halted = true ∧ target.pc = 21 ∧
      target.inputTape =
        { Tape.ofBits rest with
          left := payload.reverse.map some ++
            some false :: List.replicate count (some true) ++ before } ∧
      target.outputTape = checkTape 0 count := by
  let input := (headerSuccess before count (payload ++ rest)).inputTape
  let sourceStart :=
    (rewindBitstringStart (List.replicate (3 * count) false) input).swapTapes
  let sourceFinish :=
    (rewindBitstringFinish (List.replicate (3 * count) false) input).swapTapes
  have hHeader : RunsFor program (start before count (frame payload ++ rest))
      (headerSuccess before count (payload ++ rest)) (7 * count + 3) := by
    simpa [start, frame, hLength] using
      header_run_valid before 0 count (payload ++ rest)
  have hStart : headerSuccess before count (payload ++ rest) =
      sourceStart.rebasePc headCode.length := by
    simp [headerSuccess, sourceStart, input, counterTape, headCode,
      rewindBitstringStart, Configuration.swapTapes,
      Configuration.rebasePc]
  have hSource : RunsFor rewindBitstring.swapTapes sourceStart sourceFinish
      (2 * (3 * count) + 4) := by
    simpa [sourceStart, sourceFinish] using
      (rewindBitstring_runs (List.replicate (3 * count) false) input).swapTapes
  obtain ⟨rewindSteps, hRewindSteps, embedded⟩ :=
    hSource.withSubroutine_halted
      headCode rewindBitstring.swapTapes suffix 14
      (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
      (by simp [sourceStart, Configuration.swapTapes, rewindBitstringStart])
      (by simp [sourceFinish, Configuration.swapTapes, rewindBitstringFinish])
  have hMiddle : RunsFor program
      (headerSuccess before count (payload ++ rest))
      (sourceFinish.resumeAt 14) rewindSteps := by
    rw [program_eq, hStart]
    exact embedded
  have hPayloadStart : sourceFinish.resumeAt 14 =
      payloadScan before count [] count (payload ++ rest) := by
    cases count with
    | zero =>
        simp [sourceFinish, input, headerSuccess, rewindBitstringFinish,
          checkTape, payloadScan, counterTape, Configuration.swapTapes,
          Configuration.resumeAt, Tape.moveRight, Tape.ofBits]
    | succ count =>
        simp [sourceFinish, input, headerSuccess, rewindBitstringFinish,
          checkTape, payloadScan, counterTape, Configuration.swapTapes,
          Configuration.resumeAt, Tape.moveRight, Tape.ofBits,
          List.replicate_succ, Nat.mul_succ]
  have hPayload : RunsFor program (sourceFinish.resumeAt 14)
      { payloadScan before count payload 0 rest with pc := 21, halted := true }
      (7 * count + 2) := by
    rw [hPayloadStart]
    simpa [hLength] using payload_run_valid before count [] payload rest
  refine ⟨{ payloadScan before count payload 0 rest with pc := 21, halted := true },
    (7 * count + 3) + rewindSteps + (7 * count + 2), by omega,
    (hHeader.trans hMiddle).trans hPayload, rfl, rfl, ?_, ?_⟩
  · simp [payloadScan, checkTape, Tape.ofBits]
  · simp [payloadScan, checkTape, hLength]

theorem runs_any_loaded (before : List (Option Bool))
    (count : Nat) (bits : List Bool) :
    ∃ target used,
      used ≤ 20 * count + 12 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := before },
           outputTape := Tape.ofBits (List.replicate (3 * count) false) } : Configuration)
        target used ∧
      target.halted = true ∧
      target.outputTape.current =
        (if target.pc = 21 then none else some true) ∧
      (target.pc = 21 →
        ∃ payload rest,
          bits = frame payload ++ rest ∧ payload.length = count ∧
          target.inputTape.Equivalent
            { Tape.ofBits rest with
              left := payload.reverse.map some ++
                some false :: List.replicate count (some true) ++ before } ∧
          target.outputTape.Equivalent
            { left := List.replicate (3 * count) (some false) ++ [none] }) := by
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

/-- A valid three-cell frame cannot take the marked rejection branch. -/
theorem accepts_valid_loaded (before : List (Option Bool))
    (payload rest : List Bool) (count : Nat)
    (hLength : payload.length = count)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      ({ inputTape := { Tape.ofBits (frame payload ++ rest) with left := before },
         outputTape := Tape.ofBits (List.replicate (3 * count) false) } : Configuration)
      target used)
    (hHalt : target.halted = true) : target.pc = 21 := by
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

theorem haltsFrom (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (finish : Configuration)
    (run : PaddedRunsFor program (start before count bits) finish
      (20 * count + 12)) : finish.halted = true := by
  obtain ⟨target, used, hUsed, trace, hHalted, _, _⟩ := runs_any before count bits
  exact trace.haltsFrom_of_no_randomBit hHalted no_randomBit hUsed finish run

theorem haltsFrom_loaded (before : List (Option Bool))
    (count : Nat) (bits : List Bool) (finish : Configuration)
    (run : PaddedRunsFor program
      ({ inputTape := { Tape.ofBits bits with left := before },
         outputTape := Tape.ofBits (List.replicate (3 * count) false) } : Configuration)
      finish (20 * count + 12)) : finish.halted = true := by
  obtain ⟨target, used, hUsed, trace, hHalted, _, _⟩ :=
    runs_any_loaded before count bits
  exact trace.haltsFrom_of_no_randomBit hHalted no_randomBit hUsed finish run
end Machine.FrameWidthCheckThree
