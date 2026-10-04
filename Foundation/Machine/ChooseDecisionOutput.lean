import Foundation.Machine.ChooseWorkspaceClear

namespace Machine.ChooseDecisionOutput

private def acceptEntry : Nat := 1
private def acceptWrite : Nat := acceptEntry+ChooseWorkspaceClear.program.length+1
private def rejectEntry : Nat := acceptWrite+3
private def rejectWrite : Nat := rejectEntry+ChooseWorkspaceClear.program.length+1
private def choose : Program := [.branch .output rejectEntry rejectEntry acceptEntry]
private def accept : Program := ChooseWorkspaceClear.program.asSubroutine acceptEntry acceptWrite
private def writer (status : Bool) : Program := [.write .output status, .moveRight .output, .halt]
private def reject : Program := ChooseWorkspaceClear.program.asSubroutine rejectEntry rejectWrite

/-- Remember the actual status in finite control, erase the copied
workspace by native scans, and return just that decision bit. Both branches
have their own continuation, so erasure cannot destroy the remembered status.
This routine performs no acceptance test of its own. -/
def program : Program := choose ++ accept ++ writer true ++ reject ++ writer false

private def entry (status : Bool) : Nat := if status then acceptEntry else rejectEntry
private def writePc (status : Bool) : Nat := if status then acceptWrite else rejectWrite
private def before (status : Bool) : Program :=
  if status then choose else choose ++ accept ++ writer true
private def after (status : Bool) : Program :=
  if status then writer true ++ reject ++ writer false else writer false

private theorem before_length (status : Bool) : (before status).length = entry status := by
  cases status <;> simp [before, entry, choose, accept, writer,
    acceptEntry, acceptWrite, rejectEntry, Program.asSubroutine_length]
  omega

private theorem write_index (status : Bool) :
    writePc status = (before status).length+ChooseWorkspaceClear.program.length+1 := by
  rw [before_length]
  cases status <;> rfl

private theorem selected_layout (status : Bool) : program =
    Program.withSubroutine (before status) ChooseWorkspaceClear.program (after status) (writePc status) := by
  cases status <;> simp [program, before, after, accept, reject, writePc,
    Program.withSubroutine, before_length, entry, choose, writer,
    acceptEntry, acceptWrite, rejectEntry, rejectWrite, Program.asSubroutine_length, List.append_assoc]
  congr 1 <;> omega

private theorem branch_step (input output : Tape) :
    Step program ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := entry (output.current.getD false), inputTape := input, outputTape := output } : Configuration) := by
  cases hCurrent : output.current with
  | none => simp [Step, successors, next, program, choose, entry, Instruction.next, Configuration.tape, hCurrent]
  | some bit => cases bit <;>
      simp [Step, successors, next, program, choose, entry, Instruction.next, Configuration.tape, hCurrent]

private theorem writer_lookup (status : Bool) (offset : Nat) (hOffset : offset < 3) :
    program[writePc status+offset]? = (writer status)[offset]? := by
  rw [selected_layout status, write_index]
  rw [Program.withSubroutine_getElem?_suffix]
  cases status with
  | false => rfl
  | true =>
      change (writer true ++ reject ++ writer false)[offset]? = (writer true)[offset]?
      simpa only [List.append_assoc] using
        (List.getElem?_append_left (l₁ := writer true) (l₂ := reject ++ writer false)
          (i := offset) (by simpa [writer] using hOffset))

private theorem writes_run (status : Bool) (input output : Tape) :
    RunsFor program
      ({ pc := writePc status, inputTape := input, outputTape := output } : Configuration)
      ({ pc := writePc status+2, inputTape := input,
         outputTape := (output.write (some status)).moveRight, halted := true } : Configuration) 3 := by
  let written : Configuration :=
    { pc := writePc status+1, inputTape := input, outputTape := output.write (some status) }
  let moved : Configuration :=
    { pc := writePc status+2, inputTape := input, outputTape := (output.write (some status)).moveRight }
  have h₁ : Step program
      ({ pc := writePc status, inputTape := input, outputTape := output } : Configuration) written := by
    have hLookup := writer_lookup status 0 (by decide)
    simp only [Nat.add_zero, writer, List.getElem?_cons_zero] at hLookup
    simp [Step, successors, next, hLookup, Instruction.next, Configuration.advance,
      Configuration.updateTape, written]
  have h₂ : Step program written moved := by
    have hLookup := writer_lookup status 1 (by decide)
    simp only [writer, List.getElem?_cons_succ, List.getElem?_cons_zero] at hLookup
    simp [Step, successors, next, written, moved, hLookup, Instruction.next,
      Configuration.advance, Configuration.updateTape, Nat.add_assoc]
  have h₃ : Step program moved { moved with halted := true } := by
    have hLookup := writer_lookup status 2 (by decide)
    simp only [writer, List.getElem?_cons_succ, List.getElem?_cons_zero] at hLookup
    simp [Step, successors, next, moved, hLookup, Instruction.next]
  exact (((RunsFor.zero _).succ h₁).succ h₂).succ h₃

/-- The current workspace cell supplies the decision. All other copied
bits, both before and after the head, are actually erased. Only that one
bit is returned, and the original input tape is preserved. -/
theorem runs_bits (beforeBits rest : List Bool) (status : Bool) (input : Tape) :
    let source : Configuration :=
      { inputTape := input,
        outputTape := { Tape.ofBits (status :: rest) with left := beforeBits.reverse.map some ++ [none] } }
    ∃ target used,
      RunsFor program source target used ∧ target.halted = true ∧
      target.inputTape = input ∧ target.outputBits = [status] := by
  dsimp only
  let source : Configuration :=
    { inputTape := input,
      outputTape := { Tape.ofBits (status :: rest) with left := beforeBits.reverse.map some ++ [none] } }
  have r₁ : RunsFor program source (source.resumeAt (entry status)) 1 := by
    have h := branch_step input source.outputTape
    change Step program source (source.resumeAt (entry status)) at h
    exact (RunsFor.zero _).succ h
  obtain ⟨cleared, u₂, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    ChooseWorkspaceClear.runs_bits beforeBits (status :: rest) input
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted (before status) ChooseWorkspaceClear.program
    (after status) (writePc status) (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (source.resumeAt (entry status)) (cleared.resumeAt (writePc status)) v₂ := by
    rw [selected_layout status]
    simpa only [source, before_length, Configuration.rebasePc, Configuration.resumeAt, Nat.add_zero] using embedded₂
  have r₃ : RunsFor program (cleared.resumeAt (writePc status))
      ({ pc := writePc status+2, inputTape := cleared.inputTape,
         outputTape := (cleared.outputTape.write (some status)).moveRight, halted := true } : Configuration) 3 :=
    writes_run status cleared.inputTape cleared.outputTape
  refine ⟨_, 1+v₂+3, (r₁.trans r₂).trans r₃, rfl, hInput₂, ?_⟩
  have hBits := (hOutput₂.write (some status)).moveRight.bits
  simpa [Configuration.outputBits, Tape.bits, Tape.write, Tape.moveRight] using hBits

/-- An arbitrary malformed workspace also terminates. A blank current
cell selects rejection. Empty-result correctness is not inferred from this
termination theorem: separated old blocks require their own layout proof. -/
theorem runs_any (input output : Tape) :
    ∃ target used, used ≤ 200*(input.cells+output.cells+1) ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration) target used ∧
      target.halted = true ∧ target.inputTape = input := by
  let status := output.current.getD false
  let source : Configuration := { inputTape := input, outputTape := output }
  have r₁ : RunsFor program source (source.resumeAt (entry status)) 1 :=
    (RunsFor.zero _).succ (branch_step input output)
  obtain ⟨cleared, u₂, hu₂, run₂, hHalt₂, hInput₂⟩ := ChooseWorkspaceClear.runs_any input output
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted (before status) ChooseWorkspaceClear.program
    (after status) (writePc status) (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (source.resumeAt (entry status)) (cleared.resumeAt (writePc status)) v₂ := by
    rw [selected_layout status]
    simpa only [source, before_length, Configuration.rebasePc, Configuration.resumeAt, Nat.add_zero] using embedded₂
  have r₃ : RunsFor program (cleared.resumeAt (writePc status))
      ({ pc := writePc status+2, inputTape := cleared.inputTape,
         outputTape := (cleared.outputTape.write (some status)).moveRight, halted := true } : Configuration) 3 :=
    writes_run status cleared.inputTape cleared.outputTape
  exact ⟨_, 1+v₂+3, by omega, (r₁.trans r₂).trans r₃, rfl, hInput₂⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (600*(raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt, _⟩ := runs_any (Tape.ofBits raw) ({} : Tape)
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  apply (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono
  have hCells : (Tape.ofBits raw).cells ≤ raw.length+1 := by
    cases raw <;> simp [Tape.ofBits, Tape.cells] <;> omega
  have hEmpty : ({} : Tape).cells = 1 := rfl
  omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 600*(m+1), (PolynomiallyBounded.const 600).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.ChooseDecisionOutput
