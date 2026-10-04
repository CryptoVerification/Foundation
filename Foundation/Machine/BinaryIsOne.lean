import Foundation.Machine.BinaryEncoding
import Foundation.Machine.PolynomialTime

namespace Machine.BinaryIsOne

/-- The first little-endian bit must be one and every following bit zero.
This finite program reads one cell per step of its scan. It writes one
Boolean result on the output tape, including for empty and malformed data. -/
def program : Program :=
  [.branch .input 7 7 1,
   .moveRight .input,
   .branch .input 5 3 7,
   .moveRight .input,
   .jump 2,
   .write .output true,
   .halt,
   .write .output false,
   .halt]

def accepts : List Bool → Bool
  | true :: rest => rest.all (!·)
  | _ => false

private theorem all_false_iff_value_zero (bits : List Bool) :
    bits.all (!·) = true ↔ Binary.value bits = 0 := by
  induction bits with
  | nil => simp [Binary.value]
  | cons bit rest ih =>
      cases bit with
      | false => simpa [Binary.value] using ih
      | true => simp [Binary.value]

/-- The syntactic test agrees with the numeric value of every finite
little-endian bitstring, including redundant high zero bits. -/
theorem accepts_iff_value_one (bits : List Bool) :
    accepts bits = true ↔ Binary.value bits = 1 := by
  cases bits with
  | nil => simp [accepts, Binary.value]
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [accepts, Binary.value, Bool.toNat_false, Nat.zero_add,
            Bool.false_eq_true, false_iff]
          omega
      | true =>
          simp only [accepts, Binary.value, Bool.toNat_true]
          rw [all_false_iff_value_zero]
          omega

def budget (length : Nat) : Nat := 3 * (length + 1) + 3

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private def scan (before : List (Option Bool)) (rest : List Bool) : Configuration :=
  { pc := 2, inputTape := { Tape.ofBits rest with left := before } }

private def success (before : List (Option Bool)) : Configuration :=
  { pc := 6, inputTape := { left := before },
    outputTape := { current := some true }, halted := true }

private def failure (input : Tape) : Configuration :=
  { pc := 8, inputTape := input,
    outputTape := { current := some false }, halted := true }

private theorem scan_empty (before : List (Option Bool)) :
    RunsFor program (scan before []) (success before) 3 := by
  let start := scan before []
  let selected : Configuration := { start with pc := 5 }
  let written : Configuration :=
    { selected with pc := 6, outputTape := selected.outputTape.write (some true) }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, scan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written, scan,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (success before) := by
    simp [Step, successors, next, program, written, success, start, selected,
      scan, Instruction.next, Tape.write, Tape.ofBits]
  exact ((RunsFor.zero _).succ hBranch).succ hWrite |>.succ hHalt

private theorem scan_true (before : List (Option Bool)) (rest : List Bool) :
    RunsFor program (scan before (true :: rest))
      (failure (scan before (true :: rest)).inputTape) 3 := by
  let start := scan before (true :: rest)
  let selected : Configuration := { start with pc := 7 }
  let written : Configuration :=
    { selected with pc := 8, outputTape := selected.outputTape.write (some false) }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, scan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written, scan,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (failure start.inputTape) := by
    simp [Step, successors, next, program, written, failure, start, selected, scan,
      Instruction.next, Tape.write]
  exact ((RunsFor.zero _).succ hBranch).succ hWrite |>.succ hHalt

private theorem scan_false (before : List (Option Bool)) (rest : List Bool) :
    RunsFor program (scan before (false :: rest))
      (scan (some false :: before) rest) 3 := by
  let start := scan before (false :: rest)
  let selected : Configuration := { start with pc := 3 }
  let moved : Configuration :=
    { selected with pc := 4, inputTape := selected.inputTape.moveRight }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, program, start, selected, scan,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hMove : Step program selected moved := by
    simp [Step, successors, next, program, start, selected, moved, scan,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hJump : Step program moved (scan (some false :: before) rest) := by
    cases rest <;>
      simp [Step, successors, next, program, moved, selected, start, scan,
        Instruction.next, Tape.moveRight, Tape.ofBits]
  exact ((RunsFor.zero _).succ hBranch).succ hMove |>.succ hJump

private theorem scan_runs (before : List (Option Bool)) (rest : List Bool) :
    ∃ finish used,
      used ≤ 3 * rest.length + 3 ∧
      RunsFor program (scan before rest) finish used ∧
      finish.halted = true ∧
      finish.outputBits = [rest.all (!·)] := by
  induction rest generalizing before with
  | nil =>
      exact ⟨success before, 3, by simp, scan_empty before, rfl, rfl⟩
  | cons bit rest ih =>
      cases bit with
      | true =>
          refine ⟨failure (scan before (true :: rest)).inputTape,
            3, by simp, scan_true before rest, rfl, rfl⟩
      | false =>
          obtain ⟨finish, used, hUsed, run, hHalt, hOutput⟩ :=
            ih (some false :: before)
          refine ⟨finish, 3 + used, by simp; omega,
            (scan_false before rest).trans run, hHalt, ?_⟩
          simpa [List.all_cons] using hOutput

private theorem first_reject (bits : List Bool)
    (h : bits = [] ∨ ∃ rest, bits = false :: rest) :
    ∃ finish,
      RunsFor program (Configuration.initial bits) finish 3 ∧
      finish.halted = true ∧ finish.outputBits = [false] := by
  let start := Configuration.initial bits
  let selected : Configuration := { start with pc := 7 }
  let written : Configuration :=
    { selected with pc := 8, outputTape := selected.outputTape.write (some false) }
  have hBranch : Step program start selected := by
    rcases h with hNil | ⟨rest, hCons⟩
    · subst bits
      simp [Step, successors, next, program, start, selected,
        Instruction.next, Configuration.tape, Configuration.initial, Tape.ofBits]
    · subst bits
      simp [Step, successors, next, program, start, selected,
        Instruction.next, Configuration.tape, Configuration.initial, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, program, start, selected, written,
      Configuration.initial,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (failure start.inputTape) := by
    simp [Step, successors, next, program, written, failure, start, selected,
      Configuration.initial,
      Instruction.next, Tape.write]
  exact ⟨failure start.inputTape,
    ((RunsFor.zero _).succ hBranch).succ hWrite |>.succ hHalt,
    rfl, rfl⟩

/-- The same finite code halts on every finite input and returns its Boolean
test, with a linear bound on actual machine steps. -/
theorem runs (bits : List Bool) :
    ∃ finish used,
      used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) finish used ∧
      finish.halted = true ∧ finish.outputBits = [accepts bits] := by
  cases bits with
  | nil =>
      obtain ⟨finish, run, hHalt, hOutput⟩ := first_reject [] (Or.inl rfl)
      exact ⟨finish, 3, by simp [budget], run, hHalt, hOutput⟩
  | cons bit rest =>
      cases bit with
      | false =>
          obtain ⟨finish, run, hHalt, hOutput⟩ :=
            first_reject (false :: rest) (Or.inr ⟨rest, rfl⟩)
          exact ⟨finish, 3, by simp [budget], run, hHalt, hOutput⟩
      | true =>
          let start := Configuration.initial (true :: rest)
          let selected : Configuration := { start with pc := 1 }
          have hBranch : Step program start selected := by
            simp [Step, successors, next, program, start, selected,
              Instruction.next, Configuration.tape, Configuration.initial, Tape.ofBits]
          have hMove : Step program selected (scan [some true] rest) := by
            cases rest <;>
              simp [Step, successors, next, program, start, selected, scan,
                Configuration.initial,
                Instruction.next, Configuration.updateTape, Configuration.advance,
                Tape.moveRight, Tape.ofBits]
          obtain ⟨finish, used, hUsed, run, hHalt, hOutput⟩ :=
            scan_runs [some true] rest
          refine ⟨finish, 2 + used, ?_,
            (((RunsFor.zero _).succ hBranch).succ hMove).trans run,
            hHalt, ?_⟩
          · simp [budget]; omega
          · exact hOutput

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨finish, used, hUsed, run, hHalt, _⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem eval (bits : List Bool) :
    evalWithin program bits (budget bits.length) =
      PMF.pure (some [accepts bits]) := by
  obtain ⟨finish, used, hUsed, run, hHalt, hOutput⟩ := runs bits
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  unfold evalWithin
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 3).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
      (PolynomiallyBounded.const 3)

end Machine.BinaryIsOne
