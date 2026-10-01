import Foundation.Machine.GuardedSimulation

namespace Machine.GuardedCompiler

open VirtualCell

/-- Mathematical representation of a source tape inside a guarded region.
The saved caller prefix lies beyond the `01` boundary. This function is a
simulation postcondition, not a machine operation: preparing such a tape
from a raw input still requires an operational machine routine. -/
def encodeTape (before : List (Option Bool)) (source : Tape) : Tape :=
  pairTape (code source.current)
    (encodedLeftCells source.left ++ some true :: some false :: before)
    (encodedCells source.right)

theorem encodedLeftCells_length (cells : List (Option Bool)) :
    (encodedLeftCells cells).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [encodedLeftCells, ih, Nat.mul_add, Nat.add_assoc]

theorem encodeTape_cells (before : List (Option Bool)) (source : Tape) :
    (encodeTape before source).cells = 2 * source.cells + 2 + before.length := by
  simp [encodeTape, pairTape, Tape.cells, encodedLeftCells_length, encodedCells_length]
  omega

/-- The representation has a complete physical pair under its head even
when the source cell is blank. Logical blanks cannot be mistaken for the
unwritten physical frontier or for the reserved boundary word. -/
theorem encodeTape_pair (before : List (Option Bool)) (source : Tape) :
    (encodeTape before source).current = some (code source.current).1 ∧
    (encodeTape before source).right.head? = some (some (code source.current).2) := by
  constructor <;> rfl

theorem encodeTape_write (before : List (Option Bool)) (source : Tape) (cell : Option Bool) :
    replacePair (encodeTape before source) (code cell) =
      encodeTape before (source.write cell) := rfl

/-- Existing neighbor cells and a newly materialized frontier both agree
with the source machine's ordinary right-head movement. -/
theorem encodeTape_moveRight (before : List (Option Bool)) (source : Tape) :
    moveRightTape (encodeTape before source) = encodeTape before source.moveRight := by
  cases source with
  | mk left current right =>
      cases right with
      | nil =>
          simp [encodeTape, pairTape, encodedCells, encodedLeftCells, moveRightTape,
            Tape.moveRight, replacePair, code]
      | cons nextCell rest =>
          simp [encodeTape, pairTape, encodedCells, encodedLeftCells, moveRightTape,
            Tape.moveRight]

theorem encodeTape_rightSteps (before : List (Option Bool)) (source : Tape) :
    moveRightSteps (encodeTape before source) = if source.right = [] then 8 else 4 := by
  cases source with
  | mk left current right =>
      cases right <;> simp [moveRightSteps, encodeTape, pairTape, encodedCells, Tape.moveRight]

/-- Within the represented region a source left move is exactly two
physical left moves. The operational probe additionally inspects the pair
before returning, as established by `compile_moveLeft_probe_runs`. -/
theorem encodeTape_moveLeft_existing (before : List (Option Bool))
    (previous : Option Bool) (rest : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) :
    (encodeTape before { left := previous :: rest, current := current, right := right }).moveLeft.moveLeft =
      encodeTape before
        ({ left := previous :: rest, current := current, right := right } : Tape).moveLeft := by
  simp [encodeTape, pairTape, encodedLeftCells, encodedCells, Tape.moveLeft]

theorem encodeTape_boundary_start (which : TapeId) (before : List (Option Bool))
    (current : Option Bool) (right : List (Option Bool)) (other : Tape) :
    start (if which = .input then encodeTape before { current := current, right := right }
      else other)
      (if which = .output then encodeTape before { current := current, right := right }
        else other) = growLeftStart which before (current :: right) other := by
  cases which <;> rfl

/-- Left growth produces the exact representation of the source's left
move from its current left frontier. The source tape gains one blank;
every old logical cell and the saved caller prefix remain represented. -/
theorem encodeTape_boundary_finish (which : TapeId) (before : List (Option Bool))
    (current : Option Bool) (right : List (Option Bool)) (other : Tape) (nextPc : Nat) :
    (growLeftFinish which before (current :: right) other).resumeAt nextPc =
      ({ start
        (if which = .input then encodeTape before
          ({ current := current, right := right } : Tape).moveLeft else other)
        (if which = .output then encodeTape before
          ({ current := current, right := right } : Tape).moveLeft else other)
        with pc := nextPc } : Configuration) := by
  cases which <;> rfl

/-- A configuration representation uses the compiler's explicit address
map and the two preserved caller prefixes. It describes a correspondence
between machine states, and does not initialize either tape for free. -/
def encodeConfiguration (sourceLength : Nat) (beforeInput beforeOutput : List (Option Bool))
    (source : Configuration) : Configuration :=
  { pc := address sourceLength source.pc,
    inputTape := encodeTape beforeInput source.inputTape,
    outputTape := encodeTape beforeOutput source.outputTape,
    halted := source.halted }

theorem encodeConfiguration_write (sourceLength : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (source : Configuration)
    (which : TapeId) (cell : Option Bool) :
    (encodeConfiguration sourceLength beforeInput beforeOutput source).updateTape which
      (fun t => replacePair t (code cell)) =
      encodeConfiguration sourceLength beforeInput beforeOutput
        (source.updateTape which (fun t => t.write cell)) := by
  cases which <;> simp [encodeConfiguration, Configuration.updateTape, encodeTape_write]

theorem encodeConfiguration_moveRight (sourceLength : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (source : Configuration) (which : TapeId) :
    (encodeConfiguration sourceLength beforeInput beforeOutput source).updateTape which
      moveRightTape = encodeConfiguration sourceLength beforeInput beforeOutput
        (source.updateTape which Tape.moveRight) := by
  cases which <;> simp [encodeConfiguration, Configuration.updateTape, encodeTape_moveRight]

/-- A source write or erasure is simulated from the complete represented
source configuration. The caller prefixes remain in the representation. -/
theorem compile_write_encoded_runs (source : Program) (pc : Nat) (which : TapeId)
    (cell : Option Bool) (hpc : pc < source.length)
    (hi : source[pc] = (match cell with
      | none => .erase which | some bit => .write which bit))
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which (fun t => t.write cell)).advance) 5 := by
  have run := compile_write_runs source pc which cell hpc hi
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  cases which <;>
    simpa [encodeConfiguration, start, finish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      encodeTape_write, hPc, hActive, address_inRange source.length pc hpc.le] using run

theorem compile_randomBit_encoded_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .randomBit which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      5 = Foundation.Probability.sampleBit.map (fun bit =>
        encodeConfiguration source.length beforeInput beforeOutput
          (c.updateTape which (fun t => t.write (some bit))).advance) := by
  have hEval := compile_randomBit_eval source pc which hpc hi
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  cases which <;>
    simpa [encodeConfiguration, start, finish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      encodeTape_write, hPc, hActive, address_inRange source.length pc hpc.le] using hEval

theorem compile_write_encoded_eval (source : Program) (pc : Nat) (which : TapeId)
    (cell : Option Bool) (hpc : pc < source.length)
    (hi : source[pc] = (match cell with
      | none => .erase which | some bit => .write which bit))
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      5 = PMF.pure (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which (fun t => t.write cell)).advance) := by
  have hEval := compile_write_eval source pc which cell hpc hi
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  cases which <;>
    simpa [encodeConfiguration, start, finish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      encodeTape_write, hPc, hActive, address_inRange source.length pc hpc.le] using hEval

theorem compile_moveRight_encoded_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveRight which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (if (c.tape which).right = [] then 8 else 4) =
      PMF.pure (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which Tape.moveRight).advance) := by
  have hEval := compile_moveRight_eval source pc which hpc hi
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  by_cases hEmpty : (c.tape which).right = []
  all_goals cases which <;> simp only [Configuration.tape] at hEmpty
  all_goals
    simpa [encodeConfiguration, start, moveRightFinish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      Configuration.tape, encodeTape_moveRight, encodeTape_rightSteps,
      hPc, hActive, hEmpty, address_inRange source.length pc hpc.le] using hEval

theorem compile_branch_encoded_eval (source : Program) (pc : Nat) (which : TapeId)
    (blankPc zeroPc onePc : Nat) (hpc : pc < source.length)
    (hi : source[pc] = .branch which blankPc zeroPc onePc)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      5 = PMF.pure (encodeConfiguration source.length beforeInput beforeOutput
        ({ c with pc := match (c.tape which).current with
          | none => blankPc | some false => zeroPc | some true => onePc } : Configuration)) := by
  cases which with
  | input =>
      have hEval := compile_branch_eval source pc .input blankPc zeroPc onePc hpc hi
        c.inputTape.current
        (encodedLeftCells c.inputTape.left ++ some true :: some false :: beforeInput)
        (encodedCells c.inputTape.right) (encodeTape beforeOutput c.outputTape)
      cases hCell : c.inputTape.current with
      | none =>
          simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
            Configuration.tape, hCell, hPc, hActive,
            address_inRange source.length pc hpc.le] using hEval
      | some bit =>
          cases bit <;>
            simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
              Configuration.tape, hCell, hPc, hActive,
              address_inRange source.length pc hpc.le] using hEval
  | output =>
      have hEval := compile_branch_eval source pc .output blankPc zeroPc onePc hpc hi
        c.outputTape.current
        (encodedLeftCells c.outputTape.left ++ some true :: some false :: beforeOutput)
        (encodedCells c.outputTape.right) (encodeTape beforeInput c.inputTape)
      cases hCell : c.outputTape.current with
      | none =>
          simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
            Configuration.tape, hCell, hPc, hActive,
            address_inRange source.length pc hpc.le] using hEval
      | some bit =>
          cases bit <;>
            simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
              Configuration.tape, hCell, hPc, hActive,
              address_inRange source.length pc hpc.le] using hEval

theorem compile_moveRight_encoded_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveRight which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which Tape.moveRight).advance)
      (if (c.tape which).right = [] then 8 else 4) := by
  have run := compile_moveRight_runs source pc which hpc hi
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  by_cases hEmpty : (c.tape which).right = []
  all_goals cases which <;> simp only [Configuration.tape] at hEmpty
  all_goals
    simpa [encodeConfiguration, start, moveRightFinish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      Configuration.tape, encodeTape_moveRight, encodeTape_rightSteps,
      hPc, hActive, hEmpty, address_inRange source.length pc hpc.le] using run

theorem compile_randomBit_encoded_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .randomBit which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) (bit : Bool) :
    RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which (fun t => t.write (some bit))).advance) 5 := by
  have run := compile_randomBit_runs source pc which hpc hi bit
    (encodeTape beforeInput c.inputTape) (encodeTape beforeOutput c.outputTape)
  cases which <;>
    simpa [encodeConfiguration, start, finish, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.advance, Configuration.updateTape,
      encodeTape_write, hPc, hActive, address_inRange source.length pc hpc.le] using run

theorem compile_branch_encoded_runs (source : Program) (pc : Nat) (which : TapeId)
    (blankPc zeroPc onePc : Nat) (hpc : pc < source.length)
    (hi : source[pc] = .branch which blankPc zeroPc onePc)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (encodeConfiguration source.length beforeInput beforeOutput
        ({ c with pc := match (c.tape which).current with
          | none => blankPc | some false => zeroPc | some true => onePc } : Configuration))
      5 := by
  cases which with
  | input =>
      have run := compile_branch_runs source pc .input blankPc zeroPc onePc hpc hi
        c.inputTape.current
        (encodedLeftCells c.inputTape.left ++ some true :: some false :: beforeInput)
        (encodedCells c.inputTape.right) (encodeTape beforeOutput c.outputTape)
      cases hCell : c.inputTape.current with
      | none =>
          simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
            Configuration.tape, hCell, hPc, hActive,
            address_inRange source.length pc hpc.le] using run
      | some bit =>
          cases bit <;>
            simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
              Configuration.tape, hCell, hPc, hActive,
              address_inRange source.length pc hpc.le] using run
  | output =>
      have run := compile_branch_runs source pc .output blankPc zeroPc onePc hpc hi
        c.outputTape.current
        (encodedLeftCells c.outputTape.left ++ some true :: some false :: beforeOutput)
        (encodedCells c.outputTape.right) (encodeTape beforeInput c.inputTape)
      cases hCell : c.outputTape.current with
      | none =>
          simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
            Configuration.tape, hCell, hPc, hActive,
            address_inRange source.length pc hpc.le] using run
      | some bit =>
          cases bit <;>
            simpa [encodeConfiguration, encodeTape, pairStart, start, Configuration.rebasePc,
              Configuration.tape, hCell, hPc, hActive,
              address_inRange source.length pc hpc.le] using run

private def physicalStart (which : TapeId) (before : List (Option Bool)) (source other : Tape) :
    Configuration :=
  match which with
  | .input => start (encodeTape before source) other
  | .output => start other (encodeTape before source)

/-- Exact block cost of a represented left move. At the left frontier it
includes every transition of the guarded-region insertion routine. -/
def encodedLeftSteps (source : Tape) : Nat :=
  if source.left = [] then 17 * source.cells + 23 else 7

theorem encodedLeftSteps_le (source : Tape) :
    encodedLeftSteps source ≤ 17 * source.cells + 23 := by
  unfold encodedLeftSteps
  split <;> omega

private theorem compile_moveLeft_tape_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before : List (Option Bool)) (logical other : Tape) :
    evalConfigWithin (compile source)
      ((physicalStart which before logical other).rebasePc (blockSize * pc))
      (encodedLeftSteps logical) =
      PMF.pure ({ physicalStart which before logical.moveLeft other with
        pc := address source.length (pc + 1) } : Configuration) := by
  cases logical with
  | mk left current right =>
      cases left with
      | nil =>
          have hEval := compile_moveLeft_boundary_eval source pc which hpc hi
            before current right other
          rw [← encodeTape_boundary_start which before current right other,
            encodeTape_boundary_finish] at hEval
          cases which <;>
            simpa [physicalStart, encodedLeftSteps, Tape.cells, Nat.add_comm] using hEval
      | cons previous rest =>
          have hEval := compile_moveLeft_probe_eval source pc which hpc hi (code current)
            (code previous) (encodedLeftCells rest ++ some true :: some false :: before)
            (encodedCells right) other
          cases which <;>
            simpa [physicalStart, encodedLeftSteps, encodeTape, leftStart, leftFinish, moveLeftSteps,
              code_ne_boundary previous, pairStart, start, encodedLeftCells,
              encodedCells, Tape.moveLeft] using hEval

/-- A complete represented left-move block has the exact source successor
as its full-configuration distribution, including at the growing frontier. -/
theorem compile_moveLeft_encoded_eval (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (encodedLeftSteps (c.tape which)) =
      PMF.pure (encodeConfiguration source.length beforeInput beforeOutput
        (c.updateTape which Tape.moveLeft).advance) := by
  cases which with
  | input =>
      have hEval := compile_moveLeft_tape_eval source pc .input hpc hi
        beforeInput c.inputTape (encodeTape beforeOutput c.outputTape)
      simpa [physicalStart, encodeConfiguration, start, Configuration.rebasePc,
        Configuration.advance, Configuration.updateTape, Configuration.tape, hPc, hActive,
        address_inRange source.length pc hpc.le] using hEval
  | output =>
      have hEval := compile_moveLeft_tape_eval source pc .output hpc hi
        beforeOutput c.outputTape (encodeTape beforeInput c.inputTape)
      simpa [physicalStart, encodeConfiguration, start, Configuration.rebasePc,
        Configuration.advance, Configuration.updateTape, Configuration.tape, hPc, hActive,
        address_inRange source.length pc hpc.le] using hEval

private theorem compile_moveLeft_tape_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (before : List (Option Bool)) (logical other : Tape) :
    ∃ used, used ≤ 17 * logical.cells + 23 ∧
      RunsFor (compile source) ((physicalStart which before logical other).rebasePc (blockSize * pc))
        ({ physicalStart which before logical.moveLeft other with
          pc := address source.length (pc + 1) } : Configuration) used := by
  cases logical with
  | mk left current right =>
      cases left with
      | nil =>
          obtain ⟨used, hUsed, run⟩ := compile_moveLeft_boundary_runs source pc which hpc hi
            before current right other
          refine ⟨used, by simpa [Tape.cells, Nat.add_comm] using hUsed, ?_⟩
          rw [← encodeTape_boundary_start which before current right other,
            encodeTape_boundary_finish] at run
          cases which <;> simpa [physicalStart] using run
      | cons previous rest =>
          have run := compile_moveLeft_probe_runs source pc which hpc hi (code current)
            (code previous) (encodedLeftCells rest ++ some true :: some false :: before)
            (encodedCells right) other
          refine ⟨7, by omega, ?_⟩
          cases which <;>
            simpa [physicalStart, encodeTape, leftStart, leftFinish, moveLeftSteps,
              code_ne_boundary previous, pairStart, start, encodedLeftCells,
              encodedCells, Tape.moveLeft] using run

/-- Every source left-head move has a real compiled trace to the exact
represented source successor. At the frontier this uses linear region
growth; inside the region it uses the seven-transition probe. -/
theorem compile_moveLeft_encoded_runs (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which)
    (c : Configuration) (hPc : c.pc = pc) (hActive : c.halted = false)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ 17 * (c.tape which).cells + 23 ∧
      RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
        (encodeConfiguration source.length beforeInput beforeOutput
          (c.updateTape which Tape.moveLeft).advance) used := by
  cases which with
  | input =>
      obtain ⟨used, hUsed, run⟩ := compile_moveLeft_tape_runs source pc .input hpc hi
        beforeInput c.inputTape (encodeTape beforeOutput c.outputTape)
      refine ⟨used, hUsed, ?_⟩
      simpa [physicalStart, encodeConfiguration, start, Configuration.rebasePc,
        Configuration.advance, Configuration.updateTape, hPc, hActive,
        address_inRange source.length pc hpc.le] using run
  | output =>
      obtain ⟨used, hUsed, run⟩ := compile_moveLeft_tape_runs source pc .output hpc hi
        beforeOutput c.outputTape (encodeTape beforeInput c.inputTape)
      refine ⟨used, hUsed, ?_⟩
      simpa [physicalStart, encodeConfiguration, start, Configuration.rebasePc,
        Configuration.advance, Configuration.updateTape, hPc, hActive,
        address_inRange source.length pc hpc.le] using run

/-- Every actual source transition has a corresponding finite compiled
trace from represented states. All tape movements and boundary growth are
counted. This is forward simulation of possible branches; a worst-case
halting theorem still also needs control of every compiled branch. -/
theorem compile_step_runs (source : Program) (c d : Configuration)
    (step : Step source c d) (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ 17 * (c.inputTape.cells + c.outputTape.cells) + 23 ∧
      RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
        (encodeConfiguration source.length beforeInput beforeOutput d) used := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  by_cases hInside : c.pc < source.length
  · have hRead := List.getElem?_eq_getElem hInside
    cases hi : source[c.pc] with
    | halt =>
        have hd : d = { c with halted := true } := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        refine ⟨1, by omega, RunsFor.succ (RunsFor.zero _) ?_⟩
        simpa [encodeConfiguration] using compile_halt_step source c.pc hInside hi
          (encodeConfiguration source.length beforeInput beforeOutput c) hActive
    | jump target =>
        have hd : d = { c with pc := target } := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        refine ⟨1, by omega, RunsFor.succ (RunsFor.zero _) ?_⟩
        simpa [encodeConfiguration] using compile_jump_step source c.pc target hInside hi
          (encodeConfiguration source.length beforeInput beforeOutput c) hActive
    | branch which blankPc zeroPc onePc =>
        have hd : d = { c with pc := match (c.tape which).current with
            | none => blankPc | some false => zeroPc | some true => onePc } := by
          cases hCell : (c.tape which).current with
          | none =>
              simpa [Step, successors, next, hActive, hRead, hi, Instruction.next, hCell] using step
          | some bit =>
              cases bit <;>
                simpa [Step, successors, next, hActive, hRead, hi, Instruction.next, hCell] using step
        subst d
        exact ⟨5, by omega, compile_branch_encoded_runs source c.pc which
          blankPc zeroPc onePc hInside hi c rfl hActive beforeInput beforeOutput⟩
    | write which bit =>
        have hd : d = (c.updateTape which (fun t => t.write (some bit))).advance := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        exact ⟨5, by omega, compile_write_encoded_runs source c.pc which (some bit)
          hInside hi c rfl hActive beforeInput beforeOutput⟩
    | erase which =>
        have hd : d = (c.updateTape which (fun t => t.write none)).advance := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        exact ⟨5, by omega, compile_write_encoded_runs source c.pc which none
          hInside hi c rfl hActive beforeInput beforeOutput⟩
    | randomBit which =>
        have hd : d = (c.updateTape which (fun t => t.write (some false))).advance ∨
            d = (c.updateTape which (fun t => t.write (some true))).advance := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        rcases hd with rfl | rfl
        all_goals exact ⟨5, by omega, compile_randomBit_encoded_runs source c.pc which
          hInside hi c rfl hActive beforeInput beforeOutput _⟩
    | moveRight which =>
        have hd : d = (c.updateTape which Tape.moveRight).advance := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        refine ⟨if (c.tape which).right = [] then 8 else 4, ?_,
          compile_moveRight_encoded_runs source c.pc which hInside hi c rfl hActive
            beforeInput beforeOutput⟩
        split <;> omega
    | moveLeft which =>
        have hd : d = (c.updateTape which Tape.moveLeft).advance := by
          simpa [Step, successors, next, hActive, hRead, hi, Instruction.next] using step
        subst d
        obtain ⟨used, hUsed, run⟩ := compile_moveLeft_encoded_runs source c.pc which
          hInside hi c rfl hActive beforeInput beforeOutput
        refine ⟨used, ?_, run⟩
        cases which <;> simp only [Configuration.tape] at hUsed <;> omega
  · have hOut : source.length ≤ c.pc := by omega
    have hd : d = { c with halted := true } := by
      simpa [Step, successors, next, hActive, List.getElem?_eq_none hOut] using step
    subst d
    refine ⟨1, by omega, RunsFor.succ (RunsFor.zero _) ?_⟩
    have hPc : (encodeConfiguration source.length beforeInput beforeOutput c).pc =
        address source.length source.length := by
      change address source.length c.pc = address source.length source.length
      rw [address_outOfRange source.length c.pc hOut,
        address_inRange source.length source.length (by rfl)]
    simpa [encodeConfiguration] using compile_terminal_step source
      (encodeConfiguration source.length beforeInput beforeOutput c) hPc hActive

/-- Number of actual target transitions needed to simulate one active
source instruction. Random-bit branches have the same block length. -/
def blockSteps (source : Program) (c : Configuration) : Nat :=
  match source[c.pc]? with
  | some (.moveLeft which) => encodedLeftSteps (c.tape which)
  | some (.moveRight which) => if (c.tape which).right = [] then 8 else 4
  | some (.write _ _) | some (.erase _) | some (.randomBit _) | some (.branch _ _ _ _) => 5
  | _ => 1

theorem blockSteps_pos (source : Program) (c : Configuration) : 0 < blockSteps source c := by
  unfold blockSteps
  split <;> try omega
  · unfold encodedLeftSteps; split <;> omega
  · split <;> omega

theorem blockSteps_le (source : Program) (c : Configuration) :
    blockSteps source c ≤ 17 * (c.inputTape.cells + c.outputTape.cells) + 23 := by
  unfold blockSteps
  split <;> try omega
  · rename_i which hRead
    have hBound := encodedLeftSteps_le (c.tape which)
    cases which <;> simp only [Configuration.tape] at hBound ⊢ <;> omega
  · split <;> omega

/-- The whole distribution of one expanded instruction is precisely the
represented one-step source distribution. This covers every target branch,
not merely a chosen forward trace. Entry tapes must already be represented. -/
theorem compile_step_eval (source : Program) (c : Configuration)
    (hActive : c.halted = false) (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
      (blockSteps source c) =
      (stepPMF source c).map (encodeConfiguration source.length beforeInput beforeOutput) := by
  by_cases hInside : c.pc < source.length
  · have hRead := List.getElem?_eq_getElem hInside
    cases hi : source[c.pc] with
    | halt =>
        have hBody : 0 < (body source.length c.pc source[c.pc]).length := by simp [hi, body]
        have hLookup := compile_getElem?_body source c.pc 0 hInside hBody
        simp [hi, body] at hLookup
        simp [blockSteps, hRead, hi, evalConfigWithin, stepPMF, next,
          encodeConfiguration, hActive, hLookup, address_inRange source.length c.pc hInside.le,
          Instruction.next, PMF.pure_map]
    | jump target =>
        have hBody : 0 < (body source.length c.pc source[c.pc]).length := by simp [hi, body]
        have hLookup := compile_getElem?_body source c.pc 0 hInside hBody
        simp [hi, body] at hLookup
        simp [blockSteps, hRead, hi, evalConfigWithin, stepPMF, next,
          encodeConfiguration, hActive, hLookup, address_inRange source.length c.pc hInside.le,
          Instruction.next, PMF.pure_map]
    | branch which blankPc zeroPc onePc =>
        have hEval := compile_branch_encoded_eval source c.pc which blankPc zeroPc onePc
          hInside hi c rfl hActive beforeInput beforeOutput
        cases hCell : (c.tape which).current with
        | none =>
            simpa [blockSteps, stepPMF, next, hActive, hRead, hi, hCell,
              Instruction.next, PMF.pure_map] using hEval
        | some bit =>
            cases bit <;>
              simpa [blockSteps, stepPMF, next, hActive, hRead, hi, hCell,
                Instruction.next, PMF.pure_map] using hEval
    | write which bit =>
        simpa [blockSteps, stepPMF, next, hActive, hRead, hi, Instruction.next, PMF.pure_map]
          using compile_write_encoded_eval source c.pc which (some bit) hInside hi
            c rfl hActive beforeInput beforeOutput
    | erase which =>
        simpa [blockSteps, stepPMF, next, hActive, hRead, hi, Instruction.next, PMF.pure_map]
          using compile_write_encoded_eval source c.pc which none hInside hi
            c rfl hActive beforeInput beforeOutput
    | moveLeft which =>
        simpa [blockSteps, stepPMF, next, hActive, hRead, hi, Instruction.next, PMF.pure_map]
          using compile_moveLeft_encoded_eval source c.pc which hInside hi
            c rfl hActive beforeInput beforeOutput
    | moveRight which =>
        simpa [blockSteps, stepPMF, next, hActive, hRead, hi, Instruction.next, PMF.pure_map]
          using compile_moveRight_encoded_eval source c.pc which hInside hi
            c rfl hActive beforeInput beforeOutput
    | randomBit which =>
        have hEval := compile_randomBit_encoded_eval source c.pc which hInside hi
          c rfl hActive beforeInput beforeOutput
        simp only [blockSteps, hRead, hi] at hEval ⊢
        rw [hEval]
        simp only [stepPMF, next, hActive, Bool.false_eq_true, ↓reduceIte, hRead,
          hi, Instruction.next]
        rw [PMF.map_comp]
        congr 1
        funext bit
        cases bit <;> rfl
  · have hOutside : source.length ≤ c.pc := by omega
    have hRead : source[c.pc]? = none := by simp [hOutside]
    have hLookup := compile_getElem?_terminal source
    rw [address_inRange source.length source.length le_rfl] at hLookup
    simp [blockSteps, hRead, evalConfigWithin, stepPMF, next, encodeConfiguration,
      hActive, address_outOfRange source.length c.pc hOutside, hLookup,
      Instruction.next, PMF.pure_map]

end Machine.GuardedCompiler
