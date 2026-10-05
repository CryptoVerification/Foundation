import Foundation.Crypto.Semantics.Machine.BinaryWorkspacePadding

namespace Machine.BinaryWorkspaceAppend

/-- Extend a contiguous raw three-track input by one all-zero column.
The scan, three writes, and every head movement are native transitions.
The head finishes just beyond the new column; the caller must still rewind
it before invoking a raw arithmetic program. -/
def program : Program :=
  [.branch .input 3 1 1,
   .moveRight .input,
   .jump 0,
   .write .input false,
   .moveRight .input,
   .write .input false,
   .moveRight .input,
   .write .input false,
   .moveRight .input,
   .halt]

private def scanState (done remaining : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := done.reverse.map some } }

/-- Exact returned tape representation. The high workspace column is
physically present on the input tape; no free list append occurs in a run. -/
def finish (bits : List Bool) : Configuration :=
  { pc := 9,
    inputTape := { left := (bits ++ [false, false, false]).reverse.map some },
    halted := true }

private theorem scanBit (done rest : List Bool) (bit : Bool) :
    RunsFor program (scanState done (bit :: rest))
      (scanState (done ++ [bit]) rest) 3 := by
  let start := scanState done (bit :: rest)
  let selected : Configuration := { start with pc := 1 }
  let moved : Configuration :=
    { selected with pc := 2, inputTape := selected.inputTape.moveRight }
  have hBranch : Step program start selected := by
    cases bit <;> simp [Step, successors, next, program, start, selected,
      scanState, Tape.ofBits, Instruction.next, Configuration.tape]
  have hMove : Step program selected moved := by
    simp [Step, successors, next, program, start, selected, moved,
      scanState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hJump : Step program moved (scanState (done ++ [bit]) rest) := by
    cases rest <;> simp [Step, successors, next, program, start, selected,
      moved, scanState, Tape.ofBits, Tape.moveRight, List.reverse_append,
      Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hMove) hJump

private theorem scanEnd (done : List Bool) :
    RunsFor program (scanState done []) (finish done) 8 := by
  let s0 := scanState done []
  let s1 : Configuration := { s0 with pc := 3 }
  let s2 : Configuration := { s1 with pc := 4, inputTape := s1.inputTape.write (some false) }
  let s3 : Configuration := { s2 with pc := 5, inputTape := s2.inputTape.moveRight }
  let s4 : Configuration := { s3 with pc := 6, inputTape := s3.inputTape.write (some false) }
  let s5 : Configuration := { s4 with pc := 7, inputTape := s4.inputTape.moveRight }
  let s6 : Configuration := { s5 with pc := 8, inputTape := s5.inputTape.write (some false) }
  let s7 : Configuration := { s6 with pc := 9, inputTape := s6.inputTape.moveRight }
  have h0 : Step program s0 s1 := by
    simp [Step, successors, next, program, s0, s1, scanState,
      Tape.ofBits, Instruction.next, Configuration.tape]
  have h1 : Step program s1 s2 := by
    simp [Step, successors, next, program, s0, s1, s2, scanState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step program s2 s3 := by
    simp [Step, successors, next, program, s0, s1, s2, s3, scanState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step program s3 s4 := by
    simp [Step, successors, next, program, s0, s1, s2, s3, s4, scanState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step program s4 s5 := by
    simp [Step, successors, next, program, s0, s1, s2, s3, s4, s5, scanState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step program s5 s6 := by
    simp [Step, successors, next, program, s0, s1, s2, s3, s4, s5, s6, scanState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h6 : Step program s6 s7 := by
    simp [Step, successors, next, program, s0, s1, s2, s3, s4, s5, s6, s7,
      scanState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h7 : Step program s7 (finish done) := by
    simp [Step, successors, next, program, s0, s1, s2, s3, s4, s5, s6, s7,
      scanState, finish, Tape.ofBits, Tape.moveRight, Tape.write,
      List.reverse_append, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6) h7

private theorem scan (done remaining : List Bool) :
    RunsFor program (scanState done remaining)
      (finish (done ++ remaining)) (3 * remaining.length + 8) := by
  induction remaining generalizing done with
  | nil => simpa using scanEnd done
  | cons bit rest ih =>
      have run := (scanBit done rest bit).trans (ih (done ++ [bit]))
      convert run using 1 <;> simp [List.append_assoc] <;> omega

/-- Exact native trace on every finite raw bitstring. -/
theorem runs (bits : List Bool) :
    RunsFor program (Configuration.initial bits) (finish bits)
      (3 * bits.length + 8) := by
  have hStart : scanState [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  simpa [hStart] using scan [] bits

private def withSaved (saved : List (Option Bool)) (c : Configuration) : Configuration :=
  { c with inputTape := { c.inputTape with left := c.inputTape.left ++ saved } }

private theorem moveRight_withSaved (saved : List (Option Bool)) (t : Tape) :
    ({ t with left := t.left ++ saved } : Tape).moveRight =
      { t.moveRight with left := t.moveRight.left ++ saved } := by
  cases t with
  | mk left current right => cases right <;> rfl

/-- The append code never moves left across the blank boundary preceding a
raw input. A saved caller prefix beyond that boundary therefore remains
physically present and cannot be replaced by a canonical initial tape. -/
private theorem step_withSaved (saved : List (Option Bool))
    {c d : Configuration} (h : Step program c d) :
    Step program (withSaved saved c) (withSaved saved d) := by
  have hactive : c.halted = false := by
    cases hc : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hc) h)
  cases hInstr : program[c.pc]? with
  | none =>
      have hd : d = { c with halted := true } := by
        simpa [Step, successors, next, hactive, hInstr] using h
      subst d
      simp [Step, successors, next, withSaved, hactive, hInstr]
  | some i =>
      have hi : i ∈ program := List.mem_of_getElem? hInstr
      simp [program] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Step, successors, next, withSaved,
        Instruction.next, Configuration.advance, Configuration.updateTape,
        Configuration.tape, Tape.write, moveRight_withSaved]

private theorem run_withSaved (saved : List (Option Bool))
    {c d : Configuration} {steps : Nat} (run : RunsFor program c d steps) :
    RunsFor program (withSaved saved c) (withSaved saved d) steps := by
  induction run with
  | zero => exact RunsFor.zero _
  | succ prior last ih => exact ih.succ (step_withSaved saved last)

/-- Charged append trace with an arbitrary saved prefix behind the raw input.
The output tape stays blank, and the prefix is kept on the physical input
tape rather than removed by a proof-level tape reset. -/
theorem runs_with_saved (bits : List Bool) (saved : List (Option Bool)) :
    RunsFor program
      ({ inputTape := { Tape.ofBits bits with left := saved } } : Configuration)
      ({ pc := 9,
         inputTape := { left := (bits ++ [false, false, false]).reverse.map some ++ saved },
         halted := true } : Configuration)
      (3 * bits.length + 8) := by
  have hLeft : (Tape.ofBits bits).left = [] := by
    cases bits <;> rfl
  simpa [withSaved, finish, Configuration.initial, hLeft] using
    run_withSaved saved (runs bits)

/-- Exact evaluated state, obtained from the charged deterministic trace. -/
theorem eval (bits : List Bool) :
    evalConfigWithin program (Configuration.initial bits) (3 * bits.length + 8) =
      PMF.pure (finish bits) :=
  (runs bits).evalConfigWithin_eq_pure_of_no_randomBit (by
    intro tape
    simp [program])

/-- The returned input layout is the entry layout for a charged rewind. -/
theorem finish_rewindStart (bits : List Bool) :
    (finish bits).resumeAt 0 =
      rewindBitstringStart (bits ++ [false, false, false]) ({} : Tape) := by
  rfl

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by simp [program]

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (3 * bits.length + 8) :=
  (runs bits).haltsFrom_of_no_randomBit rfl no_randomBit (Nat.le_refl _)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 3 * length + 8,
    (PolynomiallyBounded.const 3).mul PolynomiallyBounded.id |>.add
      (PolynomiallyBounded.const 8), haltsWithin⟩

@[simp] theorem finish_input (bits : List Bool) :
    (finish bits).inputTape =
      { left := (bits ++ [false, false, false]).reverse.map some } := rfl

end Machine.BinaryWorkspaceAppend
