import Foundation.Machine.PolynomialTime

namespace Machine

open Foundation.Probability

namespace VirtualCell

/-- A logical blank is `00`; a logical bit `b` is `1b`. The unused word
`01` can mark a region boundary. These are compiler data encodings, not new
machine instructions or a new computational model. -/
def code : Option Bool → Bool × Bool
  | none => (false, false)
  | some bit => (true, bit)

def boundary : Bool × Bool := (false, true)

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

theorem code_ne_boundary (cell : Option Bool) : code cell ≠ boundary := by
  cases cell <;> simp [code, boundary]

/-- Mathematical postcondition of replacing the pair under a tape head.
Only the current cell and its right neighbor are written. Implementing this
postcondition requires several ordinary bit-machine instructions below. -/
def replacePair (t : Tape) (bits : Bool × Bool) : Tape :=
  { t with current := some bits.1, right := some bits.2 :: t.right.tail }

theorem replacePair_left (t : Tape) (bits : Bool × Bool) :
    (replacePair t bits).left = t.left := rfl

theorem replacePair_tail (t : Tape) (bits : Bool × Bool) :
    (replacePair t bits).right.tail = t.right.tail := rfl

theorem write_move_write_move (t : Tape) (first second : Bool) :
    ((t.write (some first)).moveRight.write (some second)).moveLeft =
      replacePair t (first, second) := by
  cases t with
  | mk left current right => cases right <;> rfl

/-- Both tape contents are arbitrary caller data; entering a macro provides
its initial control address. No caller tape is loaded or reset for free. -/
def start (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

def finish (which : TapeId) (cell : Option Bool) (input output : Tape) : Configuration :=
  { (start input output).updateTape which (fun t => replacePair t (code cell)) with
    pc := 4
    halted := true }

/-- Five real transitions store the two-bit code of a logical cell and
restore the physical head to the first bit. The caller must place that head
on a data cell; this macro alone does not prevent arbitrary code crossing a
boundary. Region growth and the complete source-code compiler are separate
obligations. -/
def writeCell (which : TapeId) (cell : Option Bool) : Program :=
  [.write which (code cell).1, .moveRight which,
   .write which (code cell).2, .moveLeft which, .halt]

theorem writeCell_runs (which : TapeId) (cell : Option Bool) (input output : Tape) :
    RunsFor (writeCell which cell) (start input output)
      (finish which cell input output) 5 := by
  let entered := start input output
  let first : Configuration :=
    { entered.updateTape which (fun t => t.write (some (code cell).1)) with pc := 1 }
  let moved : Configuration :=
    { first.updateTape which Tape.moveRight with pc := 2 }
  let second : Configuration :=
    { moved.updateTape which (fun t => t.write (some (code cell).2)) with pc := 3 }
  let restored : Configuration :=
    { second.updateTape which Tape.moveLeft with pc := 4 }
  have hFirst : Step (writeCell which cell) entered first := by
    cases which <;> simp [Step, successors, next, writeCell, entered, first,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step (writeCell which cell) first moved := by
    cases which <;> simp [Step, successors, next, writeCell, entered, first,
      moved, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSecond : Step (writeCell which cell) moved second := by
    cases which <;> simp [Step, successors, next, writeCell, entered, first,
      moved, second, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hRestore : Step (writeCell which cell) second restored := by
    cases which <;> simp [Step, successors, next, writeCell, entered, first,
      moved, second, restored, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hHalt : Step (writeCell which cell) restored (finish which cell input output) := by
    cases which <;> simp [Step, successors, next, writeCell, entered, first,
      moved, second, restored, start, finish, Instruction.next,
      Configuration.updateTape, write_move_write_move]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hFirst) hMove) hSecond) hRestore) hHalt

private theorem writeCell_no_randomBit (which : TapeId) (cell : Option Bool)
    (tape : TapeId) : Instruction.randomBit tape ∉ writeCell which cell := by
  simp [writeCell]

theorem writeCell_eval (which : TapeId) (cell : Option Bool) (input output : Tape) :
    evalConfigWithin (writeCell which cell) (start input output) 5 =
      PMF.pure (finish which cell input output) :=
  (writeCell_runs which cell input output).evalConfigWithin_eq_pure_of_no_randomBit
    (writeCell_no_randomBit which cell)

/-- Universal branch bound from arbitrary caller tape data, not only from
the standalone input-loading convention. -/
theorem writeCell_halts_from (which : TapeId) (cell : Option Bool)
    (input output : Tape) (final : Configuration)
    (run : PaddedRunsFor (writeCell which cell) (start input output) final 5) :
    final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff (writeCell which cell)
    (start input output) final 5).mpr run
  rw [writeCell_eval] at hMem
  have hFinal : final = finish which cell input output := by simpa using hMem
  subst final
  cases which <;> rfl

theorem writeCell_haltsWithin (which : TapeId) (cell : Option Bool) (input : List Bool) :
    HaltsWithin (writeCell which cell) input 5 := by
  have halts : HaltsWith (writeCell which cell) input
      (finish which cell (Tape.ofBits input) {}).outputBits 5 :=
    ⟨_, writeCell_runs which cell (Tape.ofBits input) {}, rfl, rfl⟩
  exact halts.haltsWithin_of_no_randomBit (writeCell_no_randomBit which cell)

theorem writeCell_polynomialTime (which : TapeId) (cell : Option Bool) :
    PolynomialTime (writeCell which cell) :=
  ⟨fun _ => 5, PolynomiallyBounded.const 5, writeCell_haltsWithin which cell⟩

/-- A fresh fair machine bit becomes the data bit of an occupied logical
cell. No random choice is made by a Lean function: the middle opcode is the
original one-bit `Instruction.randomBit`. -/
def randomCell (which : TapeId) : Program :=
  [.write which true, .moveRight which, .randomBit which, .moveLeft which, .halt]

theorem randomCell_runs (which : TapeId) (bit : Bool) (input output : Tape) :
    RunsFor (randomCell which) (start input output)
      (finish which (some bit) input output) 5 := by
  let entered := start input output
  let first : Configuration :=
    { entered.updateTape which (fun t => t.write (some true)) with pc := 1 }
  let moved : Configuration :=
    { first.updateTape which Tape.moveRight with pc := 2 }
  let second : Configuration :=
    { moved.updateTape which (fun t => t.write (some bit)) with pc := 3 }
  let restored : Configuration :=
    { second.updateTape which Tape.moveLeft with pc := 4 }
  have hFirst : Step (randomCell which) entered first := by
    cases which <;> simp [Step, successors, next, randomCell, entered, first,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step (randomCell which) first moved := by
    cases which <;> simp [Step, successors, next, randomCell, entered, first,
      moved, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRandom : Step (randomCell which) moved second := by
    cases which <;> cases bit <;> simp [Step, successors, next, randomCell,
      entered, first, moved, second, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hRestore : Step (randomCell which) second restored := by
    cases which <;> simp [Step, successors, next, randomCell, entered, first,
      moved, second, restored, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hHalt : Step (randomCell which) restored (finish which (some bit) input output) := by
    cases which <;> simp [Step, successors, next, randomCell, entered, first,
      moved, second, restored, start, finish, code, Instruction.next,
      Configuration.updateTape, write_move_write_move]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hFirst) hMove) hRandom) hRestore) hHalt

private def randomChosen (which : TapeId) (bit : Bool) (input output : Tape) :
    Configuration :=
  { (((start input output).updateTape which (fun t => t.write (some true))).updateTape
      which Tape.moveRight).updateTape which (fun t => t.write (some bit)) with pc := 3 }

private theorem randomCell_eval_three (which : TapeId) (input output : Tape) :
    evalConfigWithin (randomCell which) (start input output) 3 =
      sampleBit.map (fun bit => randomChosen which bit input output) := by
  cases which <;>
    simp [evalConfigWithin, stepPMF, next, randomCell, start, randomChosen,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  all_goals congr 1; funext bit; cases bit <;> rfl

private theorem randomCell_eval_suffix (which : TapeId) (bit : Bool)
    (input output : Tape) :
    evalConfigWithin (randomCell which) (randomChosen which bit input output) 2 =
      PMF.pure (finish which (some bit) input output) := by
  cases which <;> simp [evalConfigWithin, stepPMF, next, randomCell, start,
    randomChosen, finish, code, Instruction.next, Configuration.updateTape,
    Configuration.advance, write_move_write_move]

/-- Exact fair-bit distribution after all five actual transitions, including
halt. Preservation of surrounding data holds on each branch separately. -/
theorem randomCell_eval (which : TapeId) (input output : Tape) :
    evalConfigWithin (randomCell which) (start input output) 5 =
      sampleBit.map (fun bit => finish which (some bit) input output) := by
  rw [show 5 = 3 + 2 by rfl, evalConfigWithin_add, randomCell_eval_three,
    PMF.bind_map]
  change (sampleBit.bind fun bit => evalConfigWithin (randomCell which)
    (randomChosen which bit input output) 2) =
      (sampleBit.bind fun bit => PMF.pure (finish which (some bit) input output))
  simp only [randomCell_eval_suffix]

theorem randomCell_halts_from (which : TapeId) (input output : Tape)
    (final : Configuration)
    (run : PaddedRunsFor (randomCell which) (start input output) final 5) :
    final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff (randomCell which)
    (start input output) final 5).mpr run
  rw [randomCell_eval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _, rfl⟩ := hMem
  cases which <;> rfl

theorem randomCell_haltsWithin (which : TapeId) (input : List Bool) :
    HaltsWithin (randomCell which) input 5 :=
  randomCell_halts_from which (Tape.ofBits input) {}

theorem randomCell_polynomialTime (which : TapeId) : PolynomialTime (randomCell which) :=
  ⟨fun _ => 5, PolynomiallyBounded.const 5, randomCell_haltsWithin which⟩

/-- Decode a two-bit cell into one of four caller control addresses. Five
real transitions read the pair, restore the head, and jump to the selected
address. An absent physical bit has its own explicit malformed-code target.
The caller supplies the continuation layout; no termination claim is made
for arbitrary continuation addresses. -/
def branchCell (which : TapeId) (blankPc zeroPc onePc boundaryPc malformedPc : Nat) :
    Program :=
  [.branch which malformedPc 1 5,
   .moveRight which, .branch which malformedPc 3 9,
   .moveLeft which, .jump blankPc,
   .moveRight which, .branch which malformedPc 7 11,
   .moveLeft which, .jump zeroPc,
   .moveLeft which, .jump boundaryPc,
   .moveLeft which, .jump onePc]

def branchTarget (bits : Bool × Bool) (blankPc zeroPc onePc boundaryPc : Nat) : Nat :=
  if bits.1 then (if bits.2 then onePc else zeroPc)
  else (if bits.2 then boundaryPc else blankPc)

def pairTape (bits : Bool × Bool) (before after : List (Option Bool)) : Tape :=
  { left := before, current := some bits.1, right := some bits.2 :: after }

def pairStart (which : TapeId) (bits : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) : Configuration :=
  match which with
  | .input => start (pairTape bits before after) other
  | .output => start other (pairTape bits before after)

theorem branchCell_runs (which : TapeId) (bits : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat) :
    RunsFor (branchCell which blankPc zeroPc onePc boundaryPc malformedPc)
      (pairStart which bits before after other)
      ({ pairStart which bits before after other with
        pc := branchTarget bits blankPc zeroPc onePc boundaryPc } : Configuration) 5 := by
  let program := branchCell which blankPc zeroPc onePc boundaryPc malformedPc
  let entered := pairStart which bits before after other
  let selected : Configuration := { entered with pc := if bits.1 then 5 else 1 }
  let moved : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := if bits.1 then 6 else 2 }
  let selectedBit : Configuration :=
    { moved with pc :=
      if bits.1 then (if bits.2 then 11 else 7) else (if bits.2 then 9 else 3) }
  let restored : Configuration :=
    { entered with pc :=
      if bits.1 then (if bits.2 then 12 else 8) else (if bits.2 then 10 else 4) }
  have hFirst : Step program entered selected := by
    rcases bits with ⟨first, second⟩
    cases which <;> cases first <;> simp [Step, successors, next, program,
      branchCell, entered, selected, pairStart, pairTape, start,
      Instruction.next, Configuration.tape]
  have hMove : Step program selected moved := by
    rcases bits with ⟨first, second⟩
    cases which <;> cases first <;> simp [Step, successors, next, program,
      branchCell, entered, selected, moved, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hSecond : Step program moved selectedBit := by
    rcases bits with ⟨first, second⟩
    cases which <;> cases first <;> cases second <;>
      simp [Step, successors, next, program, branchCell, entered, selected,
        moved, selectedBit, pairStart, pairTape, start, Instruction.next,
        Configuration.updateTape, Configuration.tape, Tape.moveRight]
  have hRestore : Step program selectedBit restored := by
    rcases bits with ⟨first, second⟩
    cases which <;> cases first <;> cases second <;>
      simp [Step, successors, next, program, branchCell, entered, selected,
        moved, selectedBit, restored, pairStart, pairTape, start,
        Instruction.next, Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.moveLeft]
  have hJump : Step program restored
      ({ entered with pc := branchTarget bits blankPc zeroPc onePc boundaryPc } :
        Configuration) := by
    rcases bits with ⟨first, second⟩
    cases which <;> cases first <;> cases second <;>
      simp [Step, successors, next, program, branchCell, entered, restored,
        branchTarget, pairStart, start, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hFirst) hMove) hSecond) hRestore) hJump

theorem branchTarget_code (cell : Option Bool) (blankPc zeroPc onePc boundaryPc : Nat) :
    branchTarget (code cell) blankPc zeroPc onePc boundaryPc =
      match cell with
      | none => blankPc
      | some false => zeroPc
      | some true => onePc := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem branchTarget_boundary (blankPc zeroPc onePc boundaryPc : Nat) :
    branchTarget boundary blankPc zeroPc onePc boundaryPc = boundaryPc := rfl

theorem branchCell_eval (which : TapeId) (bits : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat) :
    evalConfigWithin (branchCell which blankPc zeroPc onePc boundaryPc malformedPc)
      (pairStart which bits before after other) 5 =
      PMF.pure ({ pairStart which bits before after other with
        pc := branchTarget bits blankPc zeroPc onePc boundaryPc } : Configuration) := by
  apply (branchCell_runs which bits before after other blankPc zeroPc onePc
    boundaryPc malformedPc).evalConfigWithin_eq_pure_of_no_randomBit
  intro tape
  simp [branchCell]

/-- All cells strictly left of the macro entry head are preserved, including
a saved caller prefix or a boundary marker. The suffix after the two-cell
code is likewise unchanged. These are tape equalities, not just equal output
observations. -/
theorem finish_preserves_surroundings (which : TapeId) (cell : Option Bool)
    (input output : Tape) :
    ((finish which cell input output).tape which).left =
      ((start input output).tape which).left ∧
    ((finish which cell input output).tape which).right.tail =
      ((start input output).tape which).right.tail := by
  cases which <;> exact ⟨rfl, rfl⟩

theorem finish_preserves_other_tape (which : TapeId) (cell : Option Bool)
    (input output : Tape) :
    (finish which cell input output).tape
        (match which with | .input => .output | .output => .input) =
      (start input output).tape
        (match which with | .input => .output | .output => .input) := by
  cases which <;> rfl

/-- Advance to the next two-bit logical cell. If its first physical cell is
unwritten, initialize a logical blank with two ordinary writes. On a valid
region this case is its right frontier. Existing cells are never written.
This macro does not check a malformed second bit or grow a left frontier. -/
def moveRightCell (which : TapeId) : Program :=
  [.moveRight which, .moveRight which, .branch which 4 3 3, .halt,
   .write which false, .moveRight which, .write which false,
   .moveLeft which, .halt]

/-- Postcondition of the right-movement macro. The conditional describes
actual control branching in `moveRightCell`, not a unit-cost tape operation. -/
def moveRightTape (t : Tape) : Tape :=
  let moved := t.moveRight.moveRight
  if moved.current = none then replacePair moved (code none) else moved

def moveRightSteps (t : Tape) : Nat :=
  if t.moveRight.moveRight.current = none then 8 else 4

def moveRightFinish (which : TapeId) (input output : Tape) : Configuration :=
  { (start input output).updateTape which moveRightTape with
    pc := if (((start input output).tape which).moveRight.moveRight).current = none
      then 8 else 3
    halted := true }

/-- The step count includes the branch and the final halt. Neither moving
over the old two-bit cell nor initializing the new one is free. -/
theorem moveRightCell_runs (which : TapeId) (input output : Tape) :
    RunsFor (moveRightCell which) (start input output)
      (moveRightFinish which input output)
      (moveRightSteps ((start input output).tape which)) := by
  let entered := start input output
  let first : Configuration :=
    { entered.updateTape which Tape.moveRight with pc := 1 }
  let moved : Configuration :=
    { first.updateTape which Tape.moveRight with pc := 2 }
  have hFirst : Step (moveRightCell which) entered first := by
    cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hMove : Step (moveRightCell which) first moved := by
    cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
      moved, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPrefix : RunsFor (moveRightCell which) entered moved 2 :=
    RunsFor.succ (RunsFor.succ (RunsFor.zero _) hFirst) hMove
  by_cases hBlank : (((start input output).tape which).moveRight.moveRight).current = none
  · let selected : Configuration := { moved with pc := 4 }
    let written : Configuration :=
      { selected.updateTape which (fun t => t.write (some false)) with pc := 5 }
    let neighbor : Configuration :=
      { written.updateTape which Tape.moveRight with pc := 6 }
    let second : Configuration :=
      { neighbor.updateTape which (fun t => t.write (some false)) with pc := 7 }
    let restored : Configuration :=
      { second.updateTape which Tape.moveLeft with pc := 8 }
    have hSelect : Step (moveRightCell which) moved selected := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, moveRightCell, entered, first, moved,
        selected, start, Instruction.next, Configuration.updateTape,
        Configuration.tape, hBlank]
    have hWrite : Step (moveRightCell which) selected written := by
      cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
        moved, selected, written, start, Instruction.next, Configuration.updateTape,
        Configuration.advance]
    have hNeighbor : Step (moveRightCell which) written neighbor := by
      cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
        moved, selected, written, neighbor, start, Instruction.next,
        Configuration.updateTape, Configuration.advance]
    have hSecond : Step (moveRightCell which) neighbor second := by
      cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
        moved, selected, written, neighbor, second, start, Instruction.next,
        Configuration.updateTape, Configuration.advance]
    have hRestore : Step (moveRightCell which) second restored := by
      cases which <;> simp [Step, successors, next, moveRightCell, entered, first,
        moved, selected, written, neighbor, second, restored, start, Instruction.next,
        Configuration.updateTape, Configuration.advance]
    have hHalt : Step (moveRightCell which) restored
        (moveRightFinish which input output) := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, moveRightCell, entered, first, moved,
        selected, written, neighbor, second, restored, start, moveRightFinish,
        moveRightTape, code, hBlank, Instruction.next, Configuration.updateTape,
        Configuration.tape, write_move_write_move]
    simpa only [moveRightSteps, hBlank, if_true] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ hPrefix hSelect) hWrite) hNeighbor) hSecond)
          hRestore) hHalt
  · let selected : Configuration := { moved with pc := 3 }
    have hSelect : Step (moveRightCell which) moved selected := by
      have hRead :
          (match (((start input output).tape which).moveRight.moveRight).current with
          | none => 4 | some false => 3 | some true => 3) = 3 := by
        cases hCell : (((start input output).tape which).moveRight.moveRight).current with
        | none => exact False.elim (hBlank hCell)
        | some bit => cases bit <;> rfl
      cases which <;> simp only [Configuration.tape, start] at hRead
      all_goals simp [Step, successors, next, moveRightCell, entered, first, moved,
        selected, start, Instruction.next, Configuration.updateTape,
        Configuration.tape]
      all_goals exact hRead.symm
    have hHalt : Step (moveRightCell which) selected
        (moveRightFinish which input output) := by
      cases which <;> simp [Configuration.tape, start] at hBlank
      all_goals simp [Step, successors, next, moveRightCell, entered, first, moved,
        selected, start, moveRightFinish, moveRightTape, hBlank, Instruction.next,
        Configuration.updateTape, Configuration.tape]
    simpa only [moveRightSteps, hBlank, if_false] using
      RunsFor.succ (RunsFor.succ hPrefix hSelect) hHalt

private theorem moveRightCell_no_randomBit (which tape : TapeId) :
    Instruction.randomBit tape ∉ moveRightCell which := by
  simp [moveRightCell]

theorem moveRightCell_eval (which : TapeId) (input output : Tape) :
    evalConfigWithin (moveRightCell which) (start input output)
      (moveRightSteps ((start input output).tape which)) =
        PMF.pure (moveRightFinish which input output) :=
  (moveRightCell_runs which input output).evalConfigWithin_eq_pure_of_no_randomBit
    (moveRightCell_no_randomBit which)

theorem moveRightCell_eval_eight (which : TapeId) (input output : Tape) :
    evalConfigWithin (moveRightCell which) (start input output) 8 =
      PMF.pure (moveRightFinish which input output) := by
  have hEval := moveRightCell_eval which input output
  by_cases hBlank : (((start input output).tape which).moveRight.moveRight).current = none
  · simpa only [moveRightSteps, hBlank, if_true] using hEval
  · simp only [moveRightSteps, hBlank, if_false] at hEval
    rw [show 8 = 4 + 4 by rfl, evalConfigWithin_add, hEval, PMF.pure_bind]
    cases which <;> simp [evalConfigWithin, stepPMF, next, moveRightFinish]

/-- The same bound holds on every operational branch from arbitrary caller
tapes. The shorter existing-cell path has four actual transitions; padding
to eight is only evaluator bookkeeping after halt. -/
theorem moveRightCell_halts_from (which : TapeId) (input output : Tape)
    (final : Configuration)
    (run : PaddedRunsFor (moveRightCell which) (start input output) final 8) :
    final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff (moveRightCell which)
    (start input output) final 8).mpr run
  rw [moveRightCell_eval_eight] at hMem
  have hFinal : final = moveRightFinish which input output := by simpa using hMem
  subst final
  rfl

theorem moveRightCell_haltsWithin (which : TapeId) (input : List Bool) :
    HaltsWithin (moveRightCell which) input 8 :=
  moveRightCell_halts_from which (Tape.ofBits input) {}

theorem moveRightCell_polynomialTime (which : TapeId) :
    PolynomialTime (moveRightCell which) :=
  ⟨fun _ => 8, PolynomiallyBounded.const 8, moveRightCell_haltsWithin which⟩

/-- After moving, the two cells just crossed are recorded in `left`. Dropping
them recovers the entire old prefix, including a boundary and saved data. -/
theorem moveRightTape_preserves_prefix (t : Tape) :
    (moveRightTape t).left.drop 2 = t.left := by
  cases t with
  | mk left current right =>
      cases right with
      | nil => simp [moveRightTape, Tape.moveRight, replacePair]
      | cons cell rest =>
          cases rest with
          | nil => simp [moveRightTape, Tape.moveRight, replacePair]
          | cons nextCell after =>
              simp only [moveRightTape, Tape.moveRight]
              by_cases h : nextCell = none <;> simp [h, replacePair]

theorem moveRightFinish_preserves_other_tape (which : TapeId) (input output : Tape) :
    (moveRightFinish which input output).tape
        (match which with | .input => .output | .output => .input) =
      (start input output).tape
        (match which with | .input => .output | .output => .input) := by
  cases which <;> rfl

/-- A move within the encoded region changes only the head position. Both
old cells and all caller data remain on the tape, in the same order. -/
theorem moveRightTape_existing (cell nextCell : Option Bool)
    (before after : List (Option Bool)) :
    moveRightTape (pairTape (code cell) before
      (some (code nextCell).1 :: some (code nextCell).2 :: after)) =
    pairTape (code nextCell)
      (some (code cell).2 :: some (code cell).1 :: before) after := by
  simp [moveRightTape, pairTape, Tape.moveRight]

/-- At the right frontier, exactly one logical blank is materialized. The
new physical bits are written by `moveRightCell`, as certified by its trace. -/
theorem moveRightTape_frontier (cell : Option Bool) (before : List (Option Bool)) :
    moveRightTape (pairTape (code cell) before []) =
    pairTape (code none) (some (code cell).2 :: some (code cell).1 :: before) [] := by
  rfl

/-- Move left by one encoded cell and inspect it. A data cell continues at
`readyPc`. The reserved boundary instead restores the old head and continues
at `boundaryPc`; the caller must implement left-region growth there. This
macro never moves to the left of that boundary under the well-formed entry
condition below. Malformed physical codes have a separate control target.
Arbitrary continuation addresses carry no termination guarantee. -/
def moveLeftCell (which : TapeId) (readyPc boundaryPc malformedPc : Nat) : Program :=
  [.moveLeft which, .moveLeft which, .branch which malformedPc 3 7,
   .moveRight which, .branch which malformedPc 5 11,
   .moveLeft which, .jump readyPc,
   .moveRight which, .branch which malformedPc 9 15,
   .moveLeft which, .jump readyPc,
   .moveLeft which, .moveRight which, .moveRight which, .jump boundaryPc,
   .moveLeft which, .jump readyPc]

def leftStart (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) : Configuration :=
  pairStart which current (some previous.2 :: some previous.1 :: before) after other

def leftFinish (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) (readyPc boundaryPc : Nat) :
    Configuration :=
  if previous = boundary then
    { leftStart which current previous before after other with pc := boundaryPc }
  else
    { pairStart which previous before (some current.1 :: some current.2 :: after) other
      with pc := readyPc }

def moveLeftSteps (previous : Bool × Bool) : Nat :=
  if previous = boundary then 9 else 7

/-- Exact traces include boundary inspection and, on the boundary path,
both physical moves restoring the old head. The surrounding saved prefix
is never examined. Every used cell is explicitly present in `leftStart`. -/
theorem moveLeftCell_runs (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape)
    (readyPc boundaryPc malformedPc : Nat) :
    RunsFor (moveLeftCell which readyPc boundaryPc malformedPc)
      (leftStart which current previous before after other)
      (leftFinish which current previous before after other readyPc boundaryPc)
      (moveLeftSteps previous) := by
  let program := moveLeftCell which readyPc boundaryPc malformedPc
  let entered := leftStart which current previous before after other
  let first : Configuration :=
    { entered.updateTape which Tape.moveLeft with pc := 1 }
  let leftPair := pairStart which previous before
    (some current.1 :: some current.2 :: after) other
  let arrived : Configuration := { leftPair with pc := 2 }
  let selected : Configuration :=
    { leftPair with pc := if previous.1 then 7 else 3 }
  let moved : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := if previous.1 then 8 else 4 }
  let selectedBit : Configuration :=
    { moved with pc := if previous.1 then (if previous.2 then 15 else 9)
      else (if previous.2 then 11 else 5) }
  let restored : Configuration :=
    { leftPair with pc := if previous.1 then (if previous.2 then 16 else 10)
      else (if previous.2 then 12 else 6) }
  have hFirst : Step program entered first := by
    cases which <;> simp [Step, successors, next, program, moveLeftCell, entered,
      first, leftStart, pairStart, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hArrive : Step program first arrived := by
    cases which <;> simp [Step, successors, next, program, moveLeftCell, entered,
      first, arrived, leftPair, leftStart, pairStart, pairTape, start, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.moveLeft]
  have hSelect : Step program arrived selected := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> simp [Step, successors, next, program, moveLeftCell,
      arrived, selected, leftPair, pairStart, pairTape, start, Instruction.next,
      Configuration.tape]
  have hMove : Step program selected moved := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> simp [Step, successors, next, program, moveLeftCell,
      selected, moved, leftPair, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hRead : Step program moved selectedBit := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> cases b <;>
      simp [Step, successors, next, program, moveLeftCell, selected, moved, selectedBit,
        leftPair, pairStart, pairTape, start, Instruction.next, Configuration.updateTape,
        Configuration.tape, Tape.moveRight]
  have hRestore : Step program selectedBit restored := by
    rcases previous with ⟨a, b⟩
    cases which <;> cases a <;> cases b <;>
      simp [Step, successors, next, program, moveLeftCell, selected, moved, selectedBit,
        restored, leftPair, pairStart, pairTape, start, Instruction.next,
        Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.moveLeft]
  have hPrefix : RunsFor program entered restored 6 :=
    RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hFirst) hArrive) hSelect) hMove)
        hRead) hRestore
  rcases previous with ⟨a, b⟩
  cases a <;> cases b
  all_goals try
    apply RunsFor.succ hPrefix
    cases which <;> simp [Step, successors, next, program, moveLeftCell, restored,
      leftPair, leftFinish, boundary, pairStart, start, Instruction.next]
  let returnedFirst : Configuration :=
    { restored.updateTape which Tape.moveRight with pc := 13 }
  let returnedSecond : Configuration :=
    { returnedFirst.updateTape which Tape.moveRight with pc := 14 }
  have hReturnFirst : Step program restored returnedFirst := by
    cases which <;> simp [Step, successors, next, program, moveLeftCell, restored,
      leftPair, returnedFirst, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hReturnSecond : Step program returnedFirst returnedSecond := by
    cases which <;> simp [Step, successors, next, program, moveLeftCell, restored,
      leftPair, returnedFirst, returnedSecond, pairStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hJump : Step program returnedSecond
      (leftFinish which current (false, true) before after other readyPc boundaryPc) := by
    cases which <;> simp [Step, successors, next, program, moveLeftCell, restored,
      leftPair, returnedFirst, returnedSecond, leftFinish, leftStart, boundary,
      pairStart, pairTape, start, Instruction.next, Configuration.updateTape,
      Tape.moveRight]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ hPrefix hReturnFirst) hReturnSecond) hJump

theorem moveLeftCell_eval (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape)
    (readyPc boundaryPc malformedPc : Nat) :
    evalConfigWithin (moveLeftCell which readyPc boundaryPc malformedPc)
      (leftStart which current previous before after other) (moveLeftSteps previous) =
      PMF.pure (leftFinish which current previous before after other readyPc boundaryPc) := by
  apply (moveLeftCell_runs which current previous before after other
    readyPc boundaryPc malformedPc).evalConfigWithin_eq_pure_of_no_randomBit
  intro tape
  simp [moveLeftCell]

theorem leftFinish_preserves_saved_prefix (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) (readyPc boundaryPc : Nat) :
    ((leftFinish which current previous before after other readyPc boundaryPc).tape
      which).left.drop (if previous = boundary then 2 else 0) = before := by
  by_cases hBoundary : previous = boundary
  all_goals cases which <;>
    simp [leftFinish, hBoundary, leftStart, pairStart, pairTape, start, Configuration.tape]

theorem leftFinish_preserves_other_tape (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) (readyPc boundaryPc : Nat) :
    (leftFinish which current previous before after other readyPc boundaryPc).tape
      (match which with | .input => .output | .output => .input) = other := by
  by_cases hBoundary : previous = boundary
  all_goals cases which <;>
    simp [leftFinish, hBoundary, leftStart, pairStart, start, Configuration.tape]

end VirtualCell

end Machine
