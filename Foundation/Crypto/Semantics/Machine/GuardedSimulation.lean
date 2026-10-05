import Foundation.Crypto.Semantics.Machine.GuardedCompiler
import Foundation.Crypto.Semantics.Machine.SubroutineSimulation

namespace Machine.GuardedCompiler

/-- Operational behavior of a branch block in any surrounding finite
program with the stated local code. Continuation labels are absolute caller
addresses. No instruction elsewhere in the program is assumed deterministic. -/
theorem branchAt_runs_in (host : Program) (base : Nat) (which : TapeId)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat)
    (hCode : ∀ offset, offset < 13 →
      host[base + offset]? =
        (branchAt base which blankPc zeroPc onePc boundaryPc malformedPc)[offset]?)
    (bits : Bool × Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor host ((VirtualCell.pairStart which bits before after other).rebasePc base)
      ({ VirtualCell.pairStart which bits before after other with
        pc := VirtualCell.branchTarget bits blankPc zeroPc onePc boundaryPc } :
          Configuration) 5 := by
  let entered := (VirtualCell.pairStart which bits before after other).rebasePc base
  let selected : Configuration := { entered with pc := base + if bits.1 then 5 else 1 }
  let moved : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := base + if bits.1 then 6 else 2 }
  let selectedBit : Configuration :=
    { moved with pc := base +
      if bits.1 then (if bits.2 then 11 else 7) else (if bits.2 then 9 else 3) }
  let restored : Configuration :=
    { entered with pc := base +
      if bits.1 then (if bits.2 then 12 else 8) else (if bits.2 then 10 else 4) }
  have h0 : host[base]? = some (.branch which malformedPc (base + 1) (base + 5)) := by
    simpa [branchAt] using hCode 0 (by decide)
  have hSteps : Step host entered selected ∧ Step host selected moved ∧
      Step host moved selectedBit ∧ Step host selectedBit restored ∧
      Step host restored
        ({ VirtualCell.pairStart which bits before after other with
          pc := VirtualCell.branchTarget bits blankPc zeroPc onePc boundaryPc } :
            Configuration) := by
    rcases bits with ⟨first, second⟩
    cases first <;> cases second <;> cases which <;>
      simp [Step, successors, next, h0, hCode, branchAt, entered, selected, moved,
        selectedBit, restored, VirtualCell.pairStart, VirtualCell.pairTape,
        VirtualCell.start, VirtualCell.branchTarget, Instruction.next,
        Configuration.rebasePc, Configuration.updateTape, Configuration.tape,
        Configuration.advance, Tape.moveRight, Tape.moveLeft, Nat.add_assoc]
  rcases hSteps with ⟨h1, h2, h3, h4, h5⟩
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5

/-- The same block has an exact pure distribution after its five actual
transitions, even if the surrounding program contains random instructions. -/
theorem branchAt_eval_in (host : Program) (base : Nat) (which : TapeId)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat)
    (hCode : ∀ offset, offset < 13 →
      host[base + offset]? =
        (branchAt base which blankPc zeroPc onePc boundaryPc malformedPc)[offset]?)
    (bits : Bool × Bool) (before after : List (Option Bool)) (other : Tape) :
    evalConfigWithin host ((VirtualCell.pairStart which bits before after other).rebasePc base)
      5 = PMF.pure ({ VirtualCell.pairStart which bits before after other with
        pc := VirtualCell.branchTarget bits blankPc zeroPc onePc boundaryPc } :
          Configuration) := by
  have h0 : host[base]? = some (.branch which malformedPc (base + 1) (base + 5)) := by
    simpa [branchAt] using hCode 0 (by decide)
  rcases bits with ⟨first, second⟩
  cases first <;> cases second <;> cases which <;>
    simp [evalConfigWithin, stepPMF, next, h0, hCode, branchAt,
      VirtualCell.pairStart, VirtualCell.pairTape, VirtualCell.start,
      VirtualCell.branchTarget, Instruction.next, Configuration.rebasePc,
      Configuration.updateTape, Configuration.tape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft, Nat.add_assoc]

private theorem compile_branch_layout (source : Program) (pc : Nat) (which : TapeId)
    (blankPc zeroPc onePc : Nat) (hpc : pc < source.length)
    (hi : source[pc] = .branch which blankPc zeroPc onePc) :
    ∀ offset, offset < 13 →
      (compile source)[blockSize * pc + offset]? =
        (branchAt (blockSize * pc) which (address source.length blankPc)
          (address source.length zeroPc) (address source.length onePc)
          (address source.length source.length) (address source.length source.length))[offset]? := by
  intro offset hOffset
  have hBody : offset < (body source.length pc source[pc]).length := by
    simpa [hi, body, branchAt] using hOffset
  simpa [hi, body] using compile_getElem?_body source pc offset hpc hBody

/-- One source branch on a logical cell takes five compiled transitions.
Both physical tapes are restored exactly; only the compiled control target
changes. This is a local instruction simulation, not a whole-program claim. -/
theorem compile_branch_runs (source : Program) (pc : Nat) (which : TapeId)
    (blankPc zeroPc onePc : Nat) (hpc : pc < source.length)
    (hi : source[pc] = .branch which blankPc zeroPc onePc)
    (cell : Option Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor (compile source)
      ((VirtualCell.pairStart which (VirtualCell.code cell) before after other).rebasePc
        (blockSize * pc))
      ({ VirtualCell.pairStart which (VirtualCell.code cell) before after other with
        pc := address source.length
          (match cell with | none => blankPc | some false => zeroPc | some true => onePc) } :
            Configuration) 5 := by
  have run := branchAt_runs_in (compile source) (blockSize * pc) which
    (address source.length blankPc) (address source.length zeroPc)
    (address source.length onePc) (address source.length source.length)
    (address source.length source.length)
    (compile_branch_layout source pc which blankPc zeroPc onePc hpc hi)
    (VirtualCell.code cell) before after other
  cases cell with
  | none => exact run
  | some bit => cases bit <;> exact run

theorem compile_branch_eval (source : Program) (pc : Nat) (which : TapeId)
    (blankPc zeroPc onePc : Nat) (hpc : pc < source.length)
    (hi : source[pc] = .branch which blankPc zeroPc onePc)
    (cell : Option Bool) (before after : List (Option Bool)) (other : Tape) :
    evalConfigWithin (compile source)
      ((VirtualCell.pairStart which (VirtualCell.code cell) before after other).rebasePc
        (blockSize * pc)) 5 =
      PMF.pure ({ VirtualCell.pairStart which (VirtualCell.code cell) before after other with
        pc := address source.length
          (match cell with | none => blankPc | some false => zeroPc | some true => onePc) } :
            Configuration) := by
  have hEval := branchAt_eval_in (compile source) (blockSize * pc) which
    (address source.length blankPc) (address source.length zeroPc)
    (address source.length onePc) (address source.length source.length)
    (address source.length source.length)
    (compile_branch_layout source pc which blankPc zeroPc onePc hpc hi)
    (VirtualCell.code cell) before after other
  cases cell with
  | none => exact hEval
  | some bit => cases bit <;> exact hEval

theorem compile_jump_step (source : Program) (pc target : Nat)
    (hpc : pc < source.length) (hi : source[pc] = .jump target)
    (c : Configuration) (hActive : c.halted = false) :
    Step (compile source) ({ c with pc := address source.length pc } : Configuration)
      ({ c with pc := address source.length target } : Configuration) := by
  have hBody : 0 < (body source.length pc source[pc]).length := by simp [hi, body]
  have hLookup := compile_getElem?_body source pc 0 hpc hBody
  simp [hi, body] at hLookup
  simp [Step, successors, next, hActive, address_inRange source.length pc hpc.le,
    hLookup, Instruction.next]

theorem compile_halt_step (source : Program) (pc : Nat)
    (hpc : pc < source.length) (hi : source[pc] = .halt)
    (c : Configuration) (hActive : c.halted = false) :
    Step (compile source) ({ c with pc := address source.length pc } : Configuration)
      ({ c with pc := address source.length pc, halted := true } : Configuration) := by
  have hBody : 0 < (body source.length pc source[pc]).length := by simp [hi, body]
  have hLookup := compile_getElem?_body source pc 0 hpc hBody
  simp [hi, body] at hLookup
  simp [Step, successors, next, hActive, address_inRange source.length pc hpc.le,
    hLookup, Instruction.next]

theorem compile_terminal_step (source : Program) (c : Configuration)
    (hPc : c.pc = address source.length source.length) (hActive : c.halted = false) :
    Step (compile source) c ({ c with halted := true } : Configuration) := by
  simp [Step, successors, next, hActive, hPc, compile_getElem?_terminal, Instruction.next]

private def randomChosen (base : Nat) (which : TapeId) (bit : Bool)
    (input output : Tape) : Configuration :=
  { (((VirtualCell.start input output).rebasePc base).updateTape which
      (fun t => t.write (some true))).updateTape which
      (fun t => t.moveRight.write (some bit)) with pc := base + 3 }

private theorem randomAt_eval_three (host : Program) (base : Nat) (which : TapeId)
    (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which true, .moveRight which, .randomBit which,
        .moveLeft which, .jump nextPc] : Program)[offset]?) (input output : Tape) :
    evalConfigWithin host ((VirtualCell.start input output).rebasePc base) 3 =
      Foundation.Probability.sampleBit.map (fun bit => randomChosen base which bit input output) := by
  have h0 : host[base]? = some (.write which true) := by simpa using hCode 0 (by decide)
  cases which <;>
    simp [evalConfigWithin, stepPMF, next, h0, hCode, randomChosen,
      VirtualCell.start, Instruction.next, Configuration.rebasePc,
      Configuration.updateTape, Configuration.advance, Nat.add_assoc]
  all_goals congr 1; funext bit; cases bit <;> rfl

private theorem randomAt_eval_suffix (host : Program) (base : Nat) (which : TapeId)
    (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which true, .moveRight which, .randomBit which,
        .moveLeft which, .jump nextPc] : Program)[offset]?)
    (bit : Bool) (input output : Tape) :
    evalConfigWithin host (randomChosen base which bit input output) 2 =
      PMF.pure ((VirtualCell.finish which (some bit) input output).resumeAt nextPc) := by
  cases which <;>
    simp [evalConfigWithin, stepPMF, next, hCode, randomChosen, VirtualCell.start,
      VirtualCell.finish, VirtualCell.code, Instruction.next, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.updateTape, Configuration.advance,
      VirtualCell.write_move_write_move, Nat.add_assoc]

/-- Exactly one original fair-bit opcode executes in the expanded block.
The head is then restored and control continues in active caller code. No
randomness is supplied by the compiler or a mathematical tape replacement. -/
theorem randomAt_eval_in (host : Program) (base : Nat) (which : TapeId) (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which true, .moveRight which, .randomBit which,
        .moveLeft which, .jump nextPc] : Program)[offset]?) (input output : Tape) :
    evalConfigWithin host ((VirtualCell.start input output).rebasePc base) 5 =
      Foundation.Probability.sampleBit.map
        (fun bit => (VirtualCell.finish which (some bit) input output).resumeAt nextPc) := by
  rw [show 5 = 3 + 2 by rfl, evalConfigWithin_add,
    randomAt_eval_three host base which nextPc hCode input output, PMF.bind_map]
  change (Foundation.Probability.sampleBit.bind fun bit =>
    evalConfigWithin host (randomChosen base which bit input output) 2) =
      (Foundation.Probability.sampleBit.bind fun bit =>
        PMF.pure ((VirtualCell.finish which (some bit) input output).resumeAt nextPc))
  simp only [randomAt_eval_suffix host base which nextPc hCode]

theorem randomAt_runs_in (host : Program) (base : Nat) (which : TapeId) (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which true, .moveRight which, .randomBit which,
        .moveLeft which, .jump nextPc] : Program)[offset]?)
    (bit : Bool) (input output : Tape) :
    RunsFor host ((VirtualCell.start input output).rebasePc base)
      ((VirtualCell.finish which (some bit) input output).resumeAt nextPc) 5 := by
  let entered := (VirtualCell.start input output).rebasePc base
  let first : Configuration :=
    { entered.updateTape which (fun t => t.write (some true)) with pc := base + 1 }
  let moved : Configuration := { first.updateTape which Tape.moveRight with pc := base + 2 }
  let chosen : Configuration :=
    { moved.updateTape which (fun t => t.write (some bit)) with pc := base + 3 }
  let restored : Configuration :=
    { chosen.updateTape which Tape.moveLeft with pc := base + 4 }
  have h0 : host[base]? = some (.write which true) := by simpa using hCode 0 (by decide)
  have hSteps : Step host entered first ∧ Step host first moved ∧
      Step host moved chosen ∧ Step host chosen restored ∧
      Step host restored ((VirtualCell.finish which (some bit) input output).resumeAt nextPc) := by
    cases which <;> cases bit <;>
      simp [Step, successors, next, h0, hCode, entered, first, moved, chosen, restored,
        VirtualCell.start, VirtualCell.finish, VirtualCell.code, Instruction.next,
        Configuration.rebasePc, Configuration.resumeAt, Configuration.updateTape,
        Configuration.advance, VirtualCell.write_move_write_move, Nat.add_assoc]
  rcases hSteps with ⟨h1, h2, h3, h4, h5⟩
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5

private theorem compile_randomBit_layout (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .randomBit which) :
    ∀ offset, offset < 5 → (compile source)[blockSize * pc + offset]? =
      ([.write which true, .moveRight which, .randomBit which, .moveLeft which,
        .jump (address source.length (pc + 1))] : Program)[offset]? := by
  intro offset hOffset
  have hBody : offset < (body source.length pc source[pc]).length := by
    simpa [hi, body, VirtualCell.randomCell] using hOffset.trans (by decide : 5 < 6)
  have hLookup := compile_getElem?_body source pc offset hpc hBody
  interval_cases offset <;>
    simpa [hi, body, VirtualCell.randomCell, Program.asSubroutine,
      Instruction.asSubroutine] using hLookup

theorem compile_randomBit_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .randomBit which) (input output : Tape) :
    evalConfigWithin (compile source) ((VirtualCell.start input output).rebasePc
      (blockSize * pc)) 5 =
      Foundation.Probability.sampleBit.map
        (fun bit => (VirtualCell.finish which (some bit) input output).resumeAt
          (address source.length (pc + 1))) :=
  randomAt_eval_in (compile source) (blockSize * pc) which
    (address source.length (pc + 1)) (compile_randomBit_layout source pc which hpc hi)
    input output

theorem compile_randomBit_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .randomBit which)
    (bit : Bool) (input output : Tape) :
    RunsFor (compile source) ((VirtualCell.start input output).rebasePc (blockSize * pc))
      ((VirtualCell.finish which (some bit) input output).resumeAt
        (address source.length (pc + 1))) 5 :=
  randomAt_runs_in (compile source) (blockSize * pc) which
    (address source.length (pc + 1)) (compile_randomBit_layout source pc which hpc hi)
    bit input output

/-- A compiled write replaces exactly the current logical cell. The five
transitions include the return jump; caller tapes are never substituted. -/
theorem writeAt_runs_in (host : Program) (base : Nat) (which : TapeId)
    (cell : Option Bool) (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which (VirtualCell.code cell).1, .moveRight which,
        .write which (VirtualCell.code cell).2, .moveLeft which,
        .jump nextPc] : Program)[offset]?) (input output : Tape) :
    RunsFor host ((VirtualCell.start input output).rebasePc base)
      ((VirtualCell.finish which cell input output).resumeAt nextPc) 5 := by
  let entered := (VirtualCell.start input output).rebasePc base
  let first : Configuration :=
    { entered.updateTape which (fun t => t.write (some (VirtualCell.code cell).1)) with
      pc := base + 1 }
  let moved : Configuration := { first.updateTape which Tape.moveRight with pc := base + 2 }
  let second : Configuration :=
    { moved.updateTape which (fun t => t.write (some (VirtualCell.code cell).2)) with
      pc := base + 3 }
  let restored : Configuration :=
    { second.updateTape which Tape.moveLeft with pc := base + 4 }
  have h0 : host[base]? = some (.write which (VirtualCell.code cell).1) := by
    simpa using hCode 0 (by decide)
  have hSteps : Step host entered first ∧ Step host first moved ∧
      Step host moved second ∧ Step host second restored ∧
      Step host restored ((VirtualCell.finish which cell input output).resumeAt nextPc) := by
    cases which <;>
      simp [Step, successors, next, h0, hCode, entered, first, moved, second, restored,
        VirtualCell.start, VirtualCell.finish, Instruction.next, Configuration.rebasePc,
        Configuration.resumeAt, Configuration.updateTape, Configuration.advance,
        VirtualCell.write_move_write_move, Nat.add_assoc]
  rcases hSteps with ⟨h1, h2, h3, h4, h5⟩
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5

theorem writeAt_eval_in (host : Program) (base : Nat) (which : TapeId)
    (cell : Option Bool) (nextPc : Nat)
    (hCode : ∀ offset, offset < 5 → host[base + offset]? =
      ([.write which (VirtualCell.code cell).1, .moveRight which,
        .write which (VirtualCell.code cell).2, .moveLeft which,
        .jump nextPc] : Program)[offset]?) (input output : Tape) :
    evalConfigWithin host ((VirtualCell.start input output).rebasePc base) 5 =
      PMF.pure ((VirtualCell.finish which cell input output).resumeAt nextPc) := by
  have h0 : host[base]? = some (.write which (VirtualCell.code cell).1) := by
    simpa using hCode 0 (by decide)
  cases which <;>
    simp [evalConfigWithin, stepPMF, next, h0, hCode, VirtualCell.start, VirtualCell.finish,
      Instruction.next, Configuration.rebasePc, Configuration.resumeAt,
      Configuration.updateTape, Configuration.advance,
      VirtualCell.write_move_write_move, Nat.add_assoc]

private theorem compile_write_layout (source : Program) (pc : Nat) (which : TapeId)
    (cell : Option Bool) (hpc : pc < source.length)
    (hi : source[pc] = (match cell with
      | none => .erase which | some bit => .write which bit)) :
    ∀ offset, offset < 5 → (compile source)[blockSize * pc + offset]? =
      ([.write which (VirtualCell.code cell).1, .moveRight which,
        .write which (VirtualCell.code cell).2, .moveLeft which,
        .jump (address source.length (pc + 1))] : Program)[offset]? := by
  intro offset hOffset
  have hBody : offset < (body source.length pc source[pc]).length := by
    cases cell <;>
      simpa [hi, body, VirtualCell.writeCell] using hOffset.trans (by decide : 5 < 6)
  have hLookup := compile_getElem?_body source pc offset hpc hBody
  cases cell <;> interval_cases offset <;>
    simpa [hi, body, VirtualCell.writeCell, VirtualCell.code, Program.asSubroutine,
      Instruction.asSubroutine] using hLookup

/-- Writing a bit and erasing a logical cell share the same verified block. -/
theorem compile_write_runs (source : Program) (pc : Nat) (which : TapeId)
    (cell : Option Bool) (hpc : pc < source.length)
    (hi : source[pc] = (match cell with
      | none => .erase which | some bit => .write which bit)) (input output : Tape) :
    RunsFor (compile source) ((VirtualCell.start input output).rebasePc (blockSize * pc))
      ((VirtualCell.finish which cell input output).resumeAt
        (address source.length (pc + 1))) 5 :=
  writeAt_runs_in (compile source) (blockSize * pc) which cell
    (address source.length (pc + 1)) (compile_write_layout source pc which cell hpc hi)
    input output

theorem compile_write_eval (source : Program) (pc : Nat) (which : TapeId)
    (cell : Option Bool) (hpc : pc < source.length)
    (hi : source[pc] = (match cell with
      | none => .erase which | some bit => .write which bit)) (input output : Tape) :
    evalConfigWithin (compile source) ((VirtualCell.start input output).rebasePc
      (blockSize * pc)) 5 =
      PMF.pure ((VirtualCell.finish which cell input output).resumeAt
        (address source.length (pc + 1))) :=
  writeAt_eval_in (compile source) (blockSize * pc) which cell
    (address source.length (pc + 1)) (compile_write_layout source pc which cell hpc hi)
    input output

section RightMovement

open VirtualCell

/-- Right movement within caller code takes four transitions for an existing
cell and eight at a blank physical frontier. The final transition is an
ordinary return jump, so the caller continues without a halted state. -/
theorem rightAt_runs_in (host : Program) (base : Nat) (which : TapeId) (nextPc : Nat)
    (hCode : ∀ offset, offset < 9 → host[base + offset]? =
      ([.moveRight which, .moveRight which,
        .branch which (base + 4) (base + 3) (base + 3), .jump nextPc,
        .write which false, .moveRight which, .write which false,
        .moveLeft which, .jump nextPc] : Program)[offset]?) (input output : Tape) :
    RunsFor host ((start input output).rebasePc base)
      ((moveRightFinish which input output).resumeAt nextPc)
      (moveRightSteps ((start input output).tape which)) := by

  let entered := (start input output).rebasePc base
  let first : Configuration :=
    { entered.updateTape which Tape.moveRight with pc := base + 1 }
  let moved : Configuration :=
    { first.updateTape which Tape.moveRight with pc := base + 2 }
  have h0 : host[base]? = some (.moveRight which) := by
    simpa using hCode 0 (by decide)
  have hFirst : Step host entered first := by
    cases which <;> simp [Step, successors, next, h0, entered, first,
      start, Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.rebasePc]
  have hMove : Step host first moved := by
    cases which <;> simp [Step, successors, next, hCode, entered, first,
      moved, start, Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.rebasePc, Nat.add_assoc]
  have hPrefix : RunsFor host entered moved 2 :=
    RunsFor.succ (RunsFor.succ (RunsFor.zero _) hFirst) hMove
  by_cases hBlank : (((start input output).tape which).moveRight.moveRight).current = none
  · let selected : Configuration := { moved with pc := base + 4 }
    let written : Configuration :=
      { selected.updateTape which (fun t => t.write (some false)) with pc := base + 5 }
    let neighbor : Configuration :=
      { written.updateTape which Tape.moveRight with pc := base + 6 }
    let second : Configuration :=
      { neighbor.updateTape which (fun t => t.write (some false)) with pc := base + 7 }
    let restored : Configuration :=
      { second.updateTape which Tape.moveLeft with pc := base + 8 }
    have hSelect : Step host moved selected := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, hCode, entered, first, moved,
        selected, start, Instruction.next, Configuration.updateTape,
        Configuration.tape, hBlank, Configuration.rebasePc]
    have hWrite : Step host selected written := by
      cases which <;> simp [Step, successors, next, hCode, entered, first,
        moved, selected, written, start, Instruction.next, Configuration.updateTape,
        Configuration.advance, Configuration.rebasePc, Nat.add_assoc]
    have hNeighbor : Step host written neighbor := by
      cases which <;> simp [Step, successors, next, hCode, entered, first,
        moved, selected, written, neighbor, start, Instruction.next,
        Configuration.updateTape, Configuration.advance, Configuration.rebasePc, Nat.add_assoc]
    have hSecond : Step host neighbor second := by
      cases which <;> simp [Step, successors, next, hCode, entered, first,
        moved, selected, written, neighbor, second, start, Instruction.next,
        Configuration.updateTape, Configuration.advance, Configuration.rebasePc, Nat.add_assoc]
    have hRestore : Step host second restored := by
      cases which <;> simp [Step, successors, next, hCode, entered, first,
        moved, selected, written, neighbor, second, restored, start, Instruction.next,
        Configuration.updateTape, Configuration.advance, Configuration.rebasePc, Nat.add_assoc]
    have hHalt : Step host restored
        ((moveRightFinish which input output).resumeAt nextPc) := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, hCode, entered, first, moved,
        selected, written, neighbor, second, restored, start, moveRightFinish,
        moveRightTape, code, hBlank, Instruction.next, Configuration.updateTape,
        Configuration.tape, write_move_write_move, Configuration.rebasePc, Configuration.resumeAt]
    simpa only [moveRightSteps, hBlank, if_true] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ hPrefix hSelect) hWrite) hNeighbor) hSecond)
          hRestore) hHalt
  · let selected : Configuration := { moved with pc := base + 3 }
    have hSelect : Step host moved selected := by
      have hRead :
          (match (((start input output).tape which).moveRight.moveRight).current with
          | none => base + 4 | some false => base + 3 | some true => base + 3) = base + 3 := by
        cases hCell : (((start input output).tape which).moveRight.moveRight).current with
        | none => exact False.elim (hBlank hCell)
        | some bit => cases bit <;> rfl
      cases which <;> simp only [Configuration.tape, start] at hRead
      all_goals simp [Step, successors, next, hCode, entered, first, moved,
        selected, start, Instruction.next, Configuration.updateTape,
        Configuration.tape, Configuration.rebasePc]
      all_goals exact hRead.symm
    have hHalt : Step host selected
        ((moveRightFinish which input output).resumeAt nextPc) := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, hCode, entered, first, moved,
        selected, start, moveRightFinish, moveRightTape, hBlank, Instruction.next,
        Configuration.updateTape, Configuration.tape, Configuration.rebasePc, Configuration.resumeAt]
    simpa only [moveRightSteps, hBlank, if_false] using
      RunsFor.succ (RunsFor.succ hPrefix hSelect) hHalt


theorem rightAt_eval_in (host : Program) (base : Nat) (which : TapeId) (nextPc : Nat)
    (hCode : ∀ offset, offset < 9 → host[base + offset]? =
      ([.moveRight which, .moveRight which,
        .branch which (base + 4) (base + 3) (base + 3), .jump nextPc,
        .write which false, .moveRight which, .write which false,
        .moveLeft which, .jump nextPc] : Program)[offset]?) (input output : Tape) :
    evalConfigWithin host ((start input output).rebasePc base)
      (moveRightSteps ((start input output).tape which)) =
        PMF.pure ((moveRightFinish which input output).resumeAt nextPc) := by
  have h0 : host[base]? = some (.moveRight which) := by
    simpa using hCode 0 (by decide)
  by_cases hBlank : (((start input output).tape which).moveRight.moveRight).current = none
  · cases which <;> simp only [Configuration.tape, start] at hBlank
    all_goals simp [evalConfigWithin, moveRightSteps, stepPMF, next, h0, hCode,
      start, moveRightFinish, moveRightTape, code, hBlank, Instruction.next,
      Configuration.updateTape, Configuration.tape, Configuration.advance,
      Configuration.rebasePc, Configuration.resumeAt, write_move_write_move, Nat.add_assoc]
  · have hCell : ∃ bit,
        (((start input output).tape which).moveRight.moveRight).current = some bit :=
      Option.ne_none_iff_exists'.mp hBlank
    rcases hCell with ⟨bit, hCell⟩
    cases which <;> simp only [Configuration.tape, start] at hCell hBlank
    all_goals cases bit <;>
      simp [evalConfigWithin, moveRightSteps, stepPMF, next, h0, hCode,
        start, moveRightFinish, moveRightTape, hCell, Instruction.next,
        Configuration.updateTape, Configuration.tape, Configuration.advance,
        Configuration.rebasePc, Configuration.resumeAt, Nat.add_assoc]

private theorem compile_moveRight_layout (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveRight which) :
    ∀ offset, offset < 9 → (compile source)[blockSize * pc + offset]? =
      ([.moveRight which, .moveRight which,
        .branch which (blockSize * pc + 4) (blockSize * pc + 3) (blockSize * pc + 3),
        .jump (address source.length (pc + 1)), .write which false, .moveRight which,
        .write which false, .moveLeft which,
        .jump (address source.length (pc + 1))] : Program)[offset]? := by
  intro offset hOffset
  have hBody : offset < (body source.length pc source[pc]).length := by
    simpa [hi, body, moveRightCell] using hOffset.trans (by decide : 9 < 10)
  have hLookup := compile_getElem?_body source pc offset hpc hBody
  interval_cases offset <;>
    simpa [hi, body, moveRightCell, Program.asSubroutine, Instruction.asSubroutine]
      using hLookup

theorem compile_moveRight_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveRight which) (input output : Tape) :
    RunsFor (compile source) ((start input output).rebasePc (blockSize * pc))
      ((moveRightFinish which input output).resumeAt (address source.length (pc + 1)))
      (moveRightSteps ((start input output).tape which)) :=
  rightAt_runs_in (compile source) (blockSize * pc) which
    (address source.length (pc + 1)) (compile_moveRight_layout source pc which hpc hi)
    input output

theorem compile_moveRight_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveRight which) (input output : Tape) :
    evalConfigWithin (compile source) ((start input output).rebasePc (blockSize * pc))
      (moveRightSteps ((start input output).tape which)) =
        PMF.pure ((moveRightFinish which input output).resumeAt
          (address source.length (pc + 1))) :=
  rightAt_eval_in (compile source) (blockSize * pc) which
    (address source.length (pc + 1)) (compile_moveRight_layout source pc which hpc hi)
    input output

end RightMovement

section LeftMovement

open VirtualCell

/-- Inspect the preceding pair in actual caller code. A valid logical cell
is reached in seven transitions. A boundary word is detected in nine,
with the head restored before entering the growth continuation. -/
theorem leftAt_runs_in (host : Program) (base : Nat) (which : TapeId)
    (current previous : Bool × Bool) (before after : List (Option Bool)) (other : Tape)
    (readyPc boundaryPc malformedPc : Nat)
    (hCode : ∀ offset, offset < 17 → host[base + offset]? =
      (leftAt base which readyPc boundaryPc malformedPc)[offset]?) :
    RunsFor host ((leftStart which current previous before after other).rebasePc base)
      (leftFinish which current previous before after other readyPc boundaryPc)
      (moveLeftSteps previous) := by

  let entered := (leftStart which current previous before after other).rebasePc base
  let first : Configuration :=
    { entered.updateTape which Tape.moveLeft with pc := base + 1 }
  let leftPair := pairStart which previous before
    (some current.1 :: some current.2 :: after) other
  let arrived : Configuration := { leftPair with pc := base + 2 }
  let selected : Configuration :=
    { leftPair with pc := base + if previous.1 then 7 else 3 }
  let moved : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := base + if previous.1 then 8 else 4 }
  let selectedBit : Configuration :=
    { moved with pc := base + if previous.1 then (if previous.2 then 15 else 9)
      else (if previous.2 then 11 else 5) }
  let restored : Configuration :=
    { leftPair with pc := base + if previous.1 then (if previous.2 then 16 else 10)
      else (if previous.2 then 12 else 6) }
  have h0 : host[base]? = some (.moveLeft which) := by
    simpa [leftAt] using hCode 0 (by decide)
  have hFirst : Step host entered first := by
    cases which <;> simp [Step, successors, next, h0, entered,
      first, leftStart, pairStart, start, Instruction.next, Configuration.updateTape,
      Configuration.advance, Configuration.rebasePc]
  have hArrive : Step host first arrived := by
    cases which <;> simp [Step, successors, next, hCode, leftAt, entered,
      first, arrived, leftPair, leftStart, pairStart, pairTape, start, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveLeft, Configuration.rebasePc, Nat.add_assoc]
  have hSelect : Step host arrived selected := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> simp [Step, successors, next, hCode, leftAt,
      arrived, selected, leftPair, pairStart, pairTape, start, Instruction.next,
      Configuration.tape]
  have hMove : Step host selected moved := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> simp [Step, successors, next, hCode, leftAt,
      selected, moved, leftPair, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance, Nat.add_assoc]
  have hRead : Step host moved selectedBit := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> cases b <;>
      simp [Step, successors, next, hCode, leftAt, selected, moved, selectedBit,
        leftPair, pairStart, pairTape, start, Instruction.next, Configuration.updateTape,
        Configuration.tape, Tape.moveRight]
  have hRestore : Step host selectedBit restored := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> cases b <;>
      simp [Step, successors, next, hCode, leftAt, selected, moved, selectedBit,
        restored, leftPair, pairStart, pairTape, start, Instruction.next,
        Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.moveLeft, Nat.add_assoc]
  have hPrefix : RunsFor host entered restored 6 :=
    RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hFirst) hArrive) hSelect) hMove)
        hRead) hRestore
  rcases previous with ⟨a, b⟩
  cases a <;> cases b
  all_goals try
    apply RunsFor.succ hPrefix
    cases which <;> simp [Step, successors, next, hCode, leftAt, restored,
      leftPair, leftFinish, boundary, pairStart, start, Instruction.next]
  let returnedFirst : Configuration :=
    { restored.updateTape which Tape.moveRight with pc := base + 13 }
  let returnedSecond : Configuration :=
    { returnedFirst.updateTape which Tape.moveRight with pc := base + 14 }
  have hReturnFirst : Step host restored returnedFirst := by
    cases which <;> simp [Step, successors, next, hCode, leftAt, restored,
      leftPair, returnedFirst, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance, Nat.add_assoc]
  have hReturnSecond : Step host returnedFirst returnedSecond := by
    cases which <;> simp [Step, successors, next, hCode, leftAt, restored,
      leftPair, returnedFirst, returnedSecond, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance, Nat.add_assoc]
  have hJump : Step host returnedSecond
      (leftFinish which current (false, true) before after other readyPc boundaryPc) := by
    cases which <;> simp [Step, successors, next, hCode, leftAt, restored,
      leftPair, returnedFirst, returnedSecond, leftFinish, leftStart, boundary,
      pairStart, pairTape, start, Instruction.next, Configuration.updateTape,
      Tape.moveRight]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ hPrefix hReturnFirst) hReturnSecond) hJump


theorem leftAt_eval_in (host : Program) (base : Nat) (which : TapeId)
    (current previous : Bool × Bool) (before after : List (Option Bool)) (other : Tape)
    (readyPc boundaryPc malformedPc : Nat)
    (hCode : ∀ offset, offset < 17 → host[base + offset]? =
      (leftAt base which readyPc boundaryPc malformedPc)[offset]?) :
    evalConfigWithin host ((leftStart which current previous before after other).rebasePc base)
      (moveLeftSteps previous) =
        PMF.pure (leftFinish which current previous before after other readyPc boundaryPc) := by
  have h0 : host[base]? = some (.moveLeft which) := by
    simpa [leftAt] using hCode 0 (by decide)
  rcases previous with ⟨first, second⟩
  cases first <;> cases second <;> cases which <;>
    simp [evalConfigWithin, moveLeftSteps, stepPMF, next, h0, hCode, leftAt,
      leftStart, leftFinish, boundary, pairStart, pairTape, start, Instruction.next,
      Configuration.rebasePc, Configuration.updateTape, Configuration.tape,
      Configuration.advance, Tape.moveLeft, Tape.moveRight, Nat.add_assoc]

private theorem compile_moveLeft_probe_layout (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which) :
    ∀ offset, offset < 17 → (compile source)[blockSize * pc + offset]? =
      (leftAt (blockSize * pc) which (address source.length (pc + 1))
        (blockSize * pc + 17) (address source.length source.length))[offset]? := by
  intro offset hOffset
  have hBody : offset < (body source.length pc source[pc]).length := by
    simpa [hi, body, leftAt, growLeftCell] using hOffset.trans (by decide : 17 < 68)
  have hLookup := compile_getElem?_body source pc offset hpc hBody
  simp only [hi, body] at hLookup
  rw [List.getElem?_append_left (by simpa [leftAt] using hOffset)] at hLookup
  exact hLookup

/-- This certifies the compiled probe, including its real return to the
growth entry. On the boundary path growth has not yet happened here. -/
theorem compile_moveLeft_probe_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (current previous : Bool × Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor (compile source)
      ((leftStart which current previous before after other).rebasePc (blockSize * pc))
      (leftFinish which current previous before after other (address source.length (pc + 1))
        (blockSize * pc + 17)) (moveLeftSteps previous) :=
  leftAt_runs_in (compile source) (blockSize * pc) which current previous before after other
    (address source.length (pc + 1)) (blockSize * pc + 17)
    (address source.length source.length) (compile_moveLeft_probe_layout source pc which hpc hi)

theorem compile_moveLeft_probe_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (current previous : Bool × Bool) (before after : List (Option Bool)) (other : Tape) :
    evalConfigWithin (compile source)
      ((leftStart which current previous before after other).rebasePc (blockSize * pc))
      (moveLeftSteps previous) =
        PMF.pure (leftFinish which current previous before after other
          (address source.length (pc + 1)) (blockSize * pc + 17)) :=
  leftAt_eval_in (compile source) (blockSize * pc) which current previous before after other
    (address source.length (pc + 1)) (blockSize * pc + 17)
    (address source.length source.length) (compile_moveLeft_probe_layout source pc which hpc hi)

/-- Exact operational invocation of the linear growth routine inside a
compiled block. Its saved caller prefix and other tape survive unchanged. -/
theorem compile_growLeft_runs_exact (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before cells : List (Option Bool)) (other : Tape) :
    RunsFor (compile source)
      ((growLeftStart which before cells other).rebasePc (blockSize * pc + 17))
      ((growLeftFinish which before cells other).resumeAt (address source.length (pc + 1)))
      (17 * cells.length + 14) := by
  let pre := blocks source.length 0 (source.take pc) ++
    leftAt (blockSize * pc) which (address source.length (pc + 1))
      (blockSize * pc + 17) (address source.length source.length)
  let suffix := blocks source.length (pc + 1) (source.drop (pc + 1)) ++ [.halt]
  have hPre : pre.length = blockSize * pc + 17 := by
    simp [pre, blocks_length, leftAt, List.length_take, Nat.min_eq_left hpc.le]
  have hHost : compile source = Program.withSubroutine pre (growLeftCell which) suffix
      (address source.length (pc + 1)) := compile_moveLeft_context source pc which hpc hi
  have run := (growLeftCell_runs which before cells other).withSubroutine_halted_of_closed
    pre (growLeftCell which) suffix (address source.length (pc + 1))
    (by cases which <;> change 0 < 50 <;> omega)
    (by cases which <;> rfl) (by cases which <;> rfl) (growLeftCell_control_closed which)
  rw [← hHost, hPre] at run
  exact run

/-- The growth invocation has a point-mass distribution at its exact return
step, even if other compiled source instructions contain random bits. -/
theorem compile_growLeft_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before cells : List (Option Bool)) (other : Tape) :
    evalConfigWithin (compile source)
      ((growLeftStart which before cells other).rebasePc (blockSize * pc + 17))
      (17 * cells.length + 14) =
        PMF.pure ((growLeftFinish which before cells other).resumeAt
          (address source.length (pc + 1))) := by
  let pre := blocks source.length 0 (source.take pc) ++
    leftAt (blockSize * pc) which (address source.length (pc + 1))
      (blockSize * pc + 17) (address source.length source.length)
  let suffix := blocks source.length (pc + 1) (source.drop (pc + 1)) ++ [.halt]
  have hPre : pre.length = blockSize * pc + 17 := by
    simp [pre, blocks_length, leftAt, List.length_take, Nat.min_eq_left hpc.le]
  have hHost : compile source = Program.withSubroutine pre (growLeftCell which) suffix
      (address source.length (pc + 1)) := compile_moveLeft_context source pc which hpc hi
  have hEval := (growLeftCell_runs which before cells other).evalConfigWithin_withSubroutine_halted_of_closed
      pre (growLeftCell which) suffix (address source.length (pc + 1))
      (by cases which <;> change 0 < 50 <;> omega)
      (by cases which <;> rfl) (by cases which <;> rfl)
      (growLeftCell_control_closed which) (growLeftCell_no_randomBit which)
  rw [← hHost, hPre] at hEval
  exact hEval

/-- A bounded trace interface for the exact growth invocation. -/
theorem compile_growLeft_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before cells : List (Option Bool)) (other : Tape) :
    ∃ used, used ≤ 17 * cells.length + 14 ∧
      RunsFor (compile source)
        ((growLeftStart which before cells other).rebasePc (blockSize * pc + 17))
        ((growLeftFinish which before cells other).resumeAt (address source.length (pc + 1)))
        used :=
  ⟨17 * cells.length + 14, le_rfl,
    compile_growLeft_runs_exact source pc which hpc hi before cells other⟩

/-- At the left boundary, the nine-transition guard probe followed by growth
takes exactly `17*m + 23` transitions for `m` old logical cells. -/
theorem compile_moveLeft_boundary_runs_exact (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before : List (Option Bool)) (cell : Option Bool) (rest : List (Option Bool))
    (other : Tape) :
    RunsFor (compile source)
      ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc))
      ((growLeftFinish which before (cell :: rest) other).resumeAt
        (address source.length (pc + 1))) (17 * (cell :: rest).length + 23) := by
  have hProbe := compile_moveLeft_probe_runs source pc which hpc hi (code cell) boundary
    before (encodedCells rest) other
  have hReturn : leftFinish which (code cell) boundary before (encodedCells rest) other
      (address source.length (pc + 1)) (blockSize * pc + 17) =
        (growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc + 17) := by
    rw [growLeftStart_cons]
    cases which <;> rfl
  rw [hReturn, ← growLeftStart_cons] at hProbe
  change RunsFor (compile source)
    ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc))
    ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc + 17)) 9 at hProbe
  have hRun := compile_growLeft_runs_exact source pc which hpc hi before (cell :: rest) other
  convert hProbe.trans hRun using 1; omega

/-- Full-configuration distribution of the boundary probe and insertion.
The caller may contain random instructions elsewhere in its code. -/
theorem compile_moveLeft_boundary_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before : List (Option Bool)) (cell : Option Bool) (rest : List (Option Bool))
    (other : Tape) :
    evalConfigWithin (compile source)
      ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc))
      (17 * (cell :: rest).length + 23) =
        PMF.pure ((growLeftFinish which before (cell :: rest) other).resumeAt
          (address source.length (pc + 1))) := by
  have hProbe := compile_moveLeft_probe_eval source pc which hpc hi (code cell) boundary
    before (encodedCells rest) other
  have hReturn : leftFinish which (code cell) boundary before (encodedCells rest) other
      (address source.length (pc + 1)) (blockSize * pc + 17) =
        (growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc + 17) := by
    rw [growLeftStart_cons]
    cases which <;> rfl
  rw [hReturn, ← growLeftStart_cons] at hProbe
  change evalConfigWithin (compile source)
    ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc)) 9 = _ at hProbe
  have hCount : 17 * (cell :: rest).length + 23 =
      9 + (17 * (cell :: rest).length + 14) := by omega
  rw [hCount, evalConfigWithin_add, hProbe, PMF.pure_bind]
  exact compile_growLeft_eval source pc which hpc hi before (cell :: rest) other

/-- Bounded-trace interface for the exact boundary insertion. This is a
local instruction simulation, not yet a whole-program runtime theorem. -/
theorem compile_moveLeft_boundary_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before : List (Option Bool)) (cell : Option Bool) (rest : List (Option Bool))
    (other : Tape) :
    ∃ used, used ≤ 17 * (cell :: rest).length + 23 ∧
      RunsFor (compile source)
        ((growLeftStart which before (cell :: rest) other).rebasePc (blockSize * pc))
        ((growLeftFinish which before (cell :: rest) other).resumeAt
          (address source.length (pc + 1))) used :=
  ⟨17 * (cell :: rest).length + 23, le_rfl,
    compile_moveLeft_boundary_runs_exact source pc which hpc hi before cell rest other⟩

end LeftMovement

end Machine.GuardedCompiler
