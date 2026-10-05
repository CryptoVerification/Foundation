import Foundation.Crypto.Semantics.Machine.VirtualCell

namespace Machine.VirtualCell

/-- Physical data cells for a finite logical region. This list describes
tape states in correctness statements; it is not a whole-list opcode. -/
def encodedCells : List (Option Bool) → List (Option Bool)
  | [] => []
  | cell :: rest => some (code cell).1 :: some (code cell).2 :: encodedCells rest

private theorem encodedCells_append (xs ys : List (Option Bool)) :
    encodedCells (xs ++ ys) = encodedCells xs ++ encodedCells ys := by
  induction xs with
  | nil => rfl
  | cons cell rest ih => simp [encodedCells, ih]

theorem encodedCells_length (cells : List (Option Bool)) :
    (encodedCells cells).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [encodedCells, ih, Nat.mul_add, Nat.add_assoc]

/-- Encoded logical cells to the left of a head, nearest first. Each pair
uses the physical reverse order, while the logical-cell order is retained. -/
def encodedLeftCells : List (Option Bool) → List (Option Bool)
  | [] => []
  | cell :: rest => some (code cell).2 :: some (code cell).1 :: encodedLeftCells rest

private def guardedPrefix (before : List (Option Bool)) : List (Option Bool) :=
  some true :: some false :: before

private def onTape (which : TapeId) (tape other : Tape) (pc : Nat := 0) : Configuration :=
  match which with
  | .input => { pc := pc, inputTape := tape, outputTape := other }
  | .output => { pc := pc, inputTape := other, outputTape := tape }

private def dataTape : List (Option Bool) → Tape
  | [] => {}
  | cell :: rest => pairTape (code cell) [] (encodedCells rest)

/-- Insert one logical blank at the left frontier of a guarded, contiguous
encoded region. First scan its pairs to the right frontier. Then copy each
pair backwards into the next pair of physical positions. Finally write
`00` just right of the unchanged boundary. All copies, scans and moves are
ordinary one-cell instructions. No caller prefix cell is copied or read.
The entry head must be at the first data pair, with the boundary immediately
to its left; the correctness theorem explicitly states this precondition. -/
def growLeftCell (which : TapeId) : Program :=
  [.branch which 4 1 1, .moveRight which, .moveRight which, .jump 0,
   .moveRight which, .moveLeft which, .moveLeft which, .moveLeft which,
   .branch which 49 9 11,
   .moveRight which, .branch which 49 13 43,
   .moveRight which, .branch which 49 23 33,
   .moveRight which, .write which false, .moveRight which, .write which false,
   .moveLeft which, .moveLeft which, .moveLeft which, .moveLeft which,
   .moveLeft which, .jump 8,
   .moveRight which, .write which true, .moveRight which, .write which false,
   .moveLeft which, .moveLeft which, .moveLeft which, .moveLeft which,
   .moveLeft which, .jump 8,
   .moveRight which, .write which true, .moveRight which, .write which true,
   .moveLeft which, .moveLeft which, .moveLeft which, .moveLeft which,
   .moveLeft which, .jump 8,
   .moveRight which, .write which false, .moveRight which, .write which false,
   .moveLeft which, .halt, .halt]

private def forwardState (which : TapeId) (before : List (Option Bool))
    (copied remaining : List (Option Bool)) (other : Tape) : Configuration :=
  onTape which { dataTape remaining with
    left := (encodedCells copied).reverse ++ guardedPrefix before } other

private def backwardState (which : TapeId) (before : List (Option Bool))
    (remaining : List (Option Bool)) (gap : Option Bool × Option Bool)
    (copied : List (Option Bool)) (other : Tape) : Configuration :=
  match remaining with
  | [] =>
      onTape which (pairTape boundary before
        (gap.1 :: gap.2 :: encodedCells copied)) other 8
  | cell :: rest =>
      onTape which (pairTape (code cell)
        (encodedLeftCells rest ++ guardedPrefix before)
        (gap.1 :: gap.2 :: encodedCells copied)) other 8

def growLeftStart (which : TapeId) (before : List (Option Bool))
    (cells : List (Option Bool)) (other : Tape) : Configuration :=
  forwardState which before [] cells other

def growLeftFinish (which : TapeId) (before : List (Option Bool))
    (cells : List (Option Bool)) (other : Tape) : Configuration :=
  { onTape which (pairTape (code none) (guardedPrefix before) (encodedCells cells)) other 48
    with halted := true }

theorem growLeftStart_cons (which : TapeId) (before : List (Option Bool))
    (cell : Option Bool) (rest : List (Option Bool)) (other : Tape) :
    growLeftStart which before (cell :: rest) other =
      leftStart which (code cell) boundary before (encodedCells rest) other := by
  cases which <;> rfl

private theorem encodedLeftCells_reverse (cells : List (Option Bool)) :
    encodedLeftCells cells.reverse = (encodedCells cells).reverse := by
  have hAppend : ∀ xs ys : List (Option Bool),
      encodedLeftCells (xs ++ ys) = encodedLeftCells xs ++ encodedLeftCells ys := by
    intro xs ys
    induction xs with
    | nil => rfl
    | cons cell rest ih => simp [encodedLeftCells, ih]
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp [List.reverse_cons, hAppend, encodedCells, encodedLeftCells, ih, List.append_assoc]

private theorem grow_scan_pair (which : TapeId) (before copied rest : List (Option Bool))
    (cell : Option Bool) (other : Tape) :
    RunsFor (growLeftCell which) (forwardState which before copied (cell :: rest) other)
      (forwardState which before (copied ++ [cell]) rest other) 4 := by
  let entered := forwardState which before copied (cell :: rest) other
  let selected : Configuration := { entered with pc := 1 }
  let first : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := 2 }
  let second : Configuration :=
    { first.updateTape which Tape.moveRight with pc := 3 }
  have hSelect : Step (growLeftCell which) entered selected := by
    cases cell with
    | none =>
        cases which <;> simp [Step, successors, next, growLeftCell, entered,
          selected, forwardState, onTape, dataTape, pairTape, code, Instruction.next,
          Configuration.tape]
    | some bit =>
        cases which <;> simp [Step, successors, next, growLeftCell, entered,
          selected, forwardState, onTape, dataTape, pairTape, code, Instruction.next,
          Configuration.tape]
  have hFirst : Step (growLeftCell which) selected first := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      first, forwardState, onTape, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hSecond : Step (growLeftCell which) first second := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      first, second, forwardState, onTape, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hJump : Step (growLeftCell which) second
      (forwardState which before (copied ++ [cell]) rest other) := by
    cases which <;> cases rest <;>
      simp [Step, successors, next, growLeftCell, entered, selected, first, second,
        forwardState, onTape, dataTape, pairTape, encodedCells, Instruction.next,
        Configuration.updateTape, Tape.moveRight, encodedCells_append,
        List.reverse_append]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hFirst) hSecond) hJump

private theorem grow_scan_end (which : TapeId) (before copied : List (Option Bool))
    (other : Tape) :
    RunsFor (growLeftCell which) (forwardState which before copied [] other)
      (backwardState which before copied.reverse (none, none) [] other) 5 := by
  let entered := forwardState which before copied [] other
  let selected : Configuration := { entered with pc := 4 }
  let extended : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := 5 }
  let restored : Configuration :=
    { extended.updateTape which Tape.moveLeft with pc := 6 }
  let second : Configuration :=
    { restored.updateTape which Tape.moveLeft with pc := 7 }
  have hSelect : Step (growLeftCell which) entered selected := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      forwardState, onTape, dataTape, Instruction.next, Configuration.tape]
  have hExtend : Step (growLeftCell which) selected extended := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      extended, forwardState, onTape, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hRestore : Step (growLeftCell which) extended restored := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      extended, restored, forwardState, onTape, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hSecond : Step (growLeftCell which) restored second := by
    cases which <;> simp [Step, successors, next, growLeftCell, entered, selected,
      extended, restored, second, forwardState, onTape, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hLast : Step (growLeftCell which) second
      (backwardState which before copied.reverse (none, none) [] other) := by
    have hReverse := encodedLeftCells_reverse copied
    cases hCells : copied.reverse with
    | nil =>
        simp only [hCells, encodedLeftCells] at hReverse
        cases which <;>
          simp [Step, successors, next, growLeftCell, entered, selected, extended,
            restored, second, forwardState, onTape, dataTape, backwardState,
            ← hReverse, encodedCells, guardedPrefix, pairTape, boundary,
            Instruction.next, Configuration.updateTape, Configuration.advance,
            Tape.moveRight, Tape.moveLeft]
    | cons cell rest =>
        simp only [hCells, encodedLeftCells] at hReverse
        cases which <;>
          simp [Step, successors, next, growLeftCell, entered, selected, extended,
            restored, second, forwardState, onTape, dataTape, backwardState,
            ← hReverse, encodedCells, guardedPrefix, pairTape,
            Instruction.next, Configuration.updateTape, Configuration.advance,
            Tape.moveRight, Tape.moveLeft]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hExtend) hRestore) hSecond) hLast

private theorem grow_scan (which : TapeId) (before copied remaining : List (Option Bool))
    (other : Tape) :
    RunsFor (growLeftCell which) (forwardState which before copied remaining other)
      (backwardState which before (copied ++ remaining).reverse (none, none) [] other)
      (4 * remaining.length + 5) := by
  induction remaining generalizing copied with
  | nil => simpa using grow_scan_end which before copied other
  | cons cell rest ih =>
      have run := (grow_scan_pair which before copied rest cell other).trans
        (ih (copied ++ [cell]))
      simpa [List.append_assoc, List.length_cons, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using run

private def copyPc : Option Bool → Nat
  | none => 13
  | some false => 23
  | some true => 33

private theorem grow_copy_pair (which : TapeId) (cell : Option Bool)
    (previous : Bool × Bool) (before after : List (Option Bool))
    (gap : Option Bool × Option Bool) (other : Tape) :
    RunsFor (growLeftCell which)
      (onTape which (pairTape (code cell)
        (some previous.2 :: some previous.1 :: before) (gap.1 :: gap.2 :: after)) other 8)
      (onTape which (pairTape previous before
        (some (code cell).1 :: some (code cell).2 ::
         some (code cell).1 :: some (code cell).2 :: after)) other 8) 13 := by
  let program := growLeftCell which
  let entered := onTape which (pairTape (code cell)
    (some previous.2 :: some previous.1 :: before) (gap.1 :: gap.2 :: after)) other 8
  let selected : Configuration := { entered with pc := if (code cell).1 then 11 else 9 }
  let read : Configuration :=
    { selected.updateTape which Tape.moveRight with pc := if (code cell).1 then 12 else 10 }
  let dispatched : Configuration := { read with pc := copyPc cell }
  let destFirst : Configuration :=
    { dispatched.updateTape which Tape.moveRight with pc := copyPc cell + 1 }
  let writtenFirst : Configuration :=
    { destFirst.updateTape which (fun t => t.write (some (code cell).1))
      with pc := copyPc cell + 2 }
  let destSecond : Configuration :=
    { writtenFirst.updateTape which Tape.moveRight with pc := copyPc cell + 3 }
  let writtenSecond : Configuration :=
    { destSecond.updateTape which (fun t => t.write (some (code cell).2))
      with pc := copyPc cell + 4 }
  let back1 : Configuration :=
    { writtenSecond.updateTape which Tape.moveLeft with pc := copyPc cell + 5 }
  let back2 : Configuration :=
    { back1.updateTape which Tape.moveLeft with pc := copyPc cell + 6 }
  let back3 : Configuration :=
    { back2.updateTape which Tape.moveLeft with pc := copyPc cell + 7 }
  let back4 : Configuration :=
    { back3.updateTape which Tape.moveLeft with pc := copyPc cell + 8 }
  let back5 : Configuration :=
    { back4.updateTape which Tape.moveLeft with pc := copyPc cell + 9 }
  let returned := onTape which (pairTape previous before
    (some (code cell).1 :: some (code cell).2 ::
     some (code cell).1 :: some (code cell).2 :: after)) other 8
  have hSteps :
      Step program entered selected ∧ Step program selected read ∧
      Step program read dispatched ∧ Step program dispatched destFirst ∧
      Step program destFirst writtenFirst ∧ Step program writtenFirst destSecond ∧
      Step program destSecond writtenSecond ∧ Step program writtenSecond back1 ∧
      Step program back1 back2 ∧ Step program back2 back3 ∧ Step program back3 back4 ∧
      Step program back4 back5 ∧ Step program back5 returned := by
    cases cell with
    | none =>
        cases which <;>
          simp [Step, successors, next, program, growLeftCell, entered, selected, read,
            dispatched, destFirst, writtenFirst, destSecond, writtenSecond, back1,
            back2, back3, back4, back5, returned, onTape, pairTape, code, copyPc,
            Instruction.next, Configuration.updateTape, Configuration.tape,
            Configuration.advance, Tape.moveRight, Tape.moveLeft, Tape.write]
    | some bit =>
        cases bit <;> cases which <;>
          simp [Step, successors, next, program, growLeftCell, entered, selected, read,
            dispatched, destFirst, writtenFirst, destSecond, writtenSecond, back1,
            back2, back3, back4, back5, returned, onTape, pairTape, code, copyPc,
            Instruction.next, Configuration.updateTape, Configuration.tape,
            Configuration.advance, Tape.moveRight, Tape.moveLeft, Tape.write]
  rcases hSteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5)
        h6) h7) h8) h9) h10) h11) h12) h13

private theorem grow_boundary (which : TapeId) (before : List (Option Bool))
    (gap : Option Bool × Option Bool) (copied : List (Option Bool)) (other : Tape) :
    RunsFor (growLeftCell which) (backwardState which before [] gap copied other)
      (growLeftFinish which before copied other) 9 := by
  let program := growLeftCell which
  let entered := backwardState which before [] gap copied other
  let selected : Configuration := { entered with pc := 9 }
  let read : Configuration := { selected.updateTape which Tape.moveRight with pc := 10 }
  let dispatched : Configuration := { read with pc := 43 }
  let destFirst : Configuration :=
    { dispatched.updateTape which Tape.moveRight with pc := 44 }
  let writtenFirst : Configuration :=
    { destFirst.updateTape which (fun t => t.write (some false)) with pc := 45 }
  let destSecond : Configuration :=
    { writtenFirst.updateTape which Tape.moveRight with pc := 46 }
  let writtenSecond : Configuration :=
    { destSecond.updateTape which (fun t => t.write (some false)) with pc := 47 }
  let restored : Configuration :=
    { writtenSecond.updateTape which Tape.moveLeft with pc := 48 }
  have hSteps :
      Step program entered selected ∧ Step program selected read ∧
      Step program read dispatched ∧ Step program dispatched destFirst ∧
      Step program destFirst writtenFirst ∧ Step program writtenFirst destSecond ∧
      Step program destSecond writtenSecond ∧ Step program writtenSecond restored ∧
      Step program restored (growLeftFinish which before copied other) := by
    cases which <;>
      simp [Step, successors, next, program, growLeftCell, entered, selected, read,
        dispatched, destFirst, writtenFirst, destSecond, writtenSecond, restored,
        backwardState, growLeftFinish, onTape, pairTape, guardedPrefix, boundary, code,
        Instruction.next, Configuration.updateTape, Configuration.tape,
        Configuration.advance, Tape.moveRight, Tape.moveLeft, Tape.write]
  rcases hSteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h1)
      h2) h3) h4) h5) h6) h7) h8) h9

private theorem grow_backward (which : TapeId) (before remaining : List (Option Bool))
    (gap : Option Bool × Option Bool) (copied : List (Option Bool)) (other : Tape) :
    RunsFor (growLeftCell which) (backwardState which before remaining gap copied other)
      (growLeftFinish which before (remaining.reverse ++ copied) other)
      (13 * remaining.length + 9) := by
  induction remaining generalizing gap copied with
  | nil => simpa using grow_boundary which before gap copied other
  | cons cell rest ih =>
      have hCopy : RunsFor (growLeftCell which)
          (backwardState which before (cell :: rest) gap copied other)
          (backwardState which before rest (some (code cell).1, some (code cell).2)
            (cell :: copied) other) 13 := by
        cases rest with
        | nil =>
            simpa [backwardState, encodedLeftCells, guardedPrefix, encodedCells, boundary]
              using grow_copy_pair which cell boundary before (encodedCells copied) gap other
        | cons previous tail =>
            simpa [backwardState, encodedLeftCells, encodedCells]
              using grow_copy_pair which cell (code previous)
                (encodedLeftCells tail ++ guardedPrefix before) (encodedCells copied) gap other
      have run := hCopy.trans
        (ih (some (code cell).1, some (code cell).2) (cell :: copied))
      simpa [List.reverse_cons, List.append_assoc, List.length_cons, Nat.mul_add,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

/-- Insert one blank without changing the saved caller prefix or the order
of any original logical cells. The exact count is linear in the logical
region length: four scan steps and thirteen copy steps per old cell, plus
fourteen frontier/guard steps, including the final halt. -/
theorem growLeftCell_runs (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) :
    RunsFor (growLeftCell which) (growLeftStart which before cells other)
      (growLeftFinish which before cells other) (17 * cells.length + 14) := by
  have scan := grow_scan which before [] cells other
  have copied := grow_backward which before cells.reverse (none, none) [] other
  have run := scan.trans copied
  have hCount : (4 * cells.length + 5) + (13 * cells.reverse.length + 9) =
      17 * cells.length + 14 := by
    simp only [List.length_reverse]
    omega
  rw [hCount] at run
  simpa [growLeftStart] using run

theorem growLeftCell_no_randomBit (which tape : TapeId) :
    Instruction.randomBit tape ∉ growLeftCell which := by simp [growLeftCell]

/-- Every active transition of the growth routine remains in its finite
code. Both success and malformed-input exits use explicit halt instructions. -/
theorem growLeftCell_control_closed (which : TapeId) (c d : Configuration)
    (hPc : c.pc < (growLeftCell which).length)
    (step : Step (growLeftCell which) c d) (_hRunning : d.halted = false) :
    d.pc < (growLeftCell which).length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 50 at hPc
  interval_cases hIndex : c.pc <;>
    cases hCell : (c.tape which).current with
    | none =>
        simp [Step, successors, next, hActive, hIndex, growLeftCell,
          Instruction.next, hCell] at step
        subst d
        cases which <;>
          simp [growLeftCell, Configuration.advance, Configuration.updateTape, hIndex]
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, hActive, hIndex, growLeftCell,
            Instruction.next, hCell] at step <;>
          subst d <;>
          cases which <;>
          simp [growLeftCell, Configuration.advance, Configuration.updateTape, hIndex]

theorem growLeftCell_eval (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) :
    evalConfigWithin (growLeftCell which) (growLeftStart which before cells other)
      (17 * cells.length + 14) = PMF.pure (growLeftFinish which before cells other) :=
  (growLeftCell_runs which before cells other).evalConfigWithin_eq_pure_of_no_randomBit
    (growLeftCell_no_randomBit which)

theorem growLeftCell_halts (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) (final : Configuration)
    (run : PaddedRunsFor (growLeftCell which) (growLeftStart which before cells other)
      final (17 * cells.length + 14)) : final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff (growLeftCell which)
    (growLeftStart which before cells other) final (17 * cells.length + 14)).mpr run
  rw [growLeftCell_eval] at hMem
  have hFinal : final = growLeftFinish which before cells other := by simpa using hMem
  subst final
  rfl

theorem growLeftFinish_preserves_prefix (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) :
    ((growLeftFinish which before cells other).tape which).left =
      some true :: some false :: before := by cases which <;> rfl

theorem growLeftFinish_preserves_other_tape (which : TapeId)
    (before cells : List (Option Bool)) (other : Tape) :
    (growLeftFinish which before cells other).tape
      (match which with | .input => .output | .output => .input) = other := by
  cases which <;> rfl

theorem growLeftFinish_cells (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) :
    ((growLeftFinish which before cells other).tape which).current = some false ∧
    ((growLeftFinish which before cells other).tape which).right =
      some false :: encodedCells cells := by cases which <;> exact ⟨rfl, rfl⟩

/-- Inserting one two-bit cell uses at most two additional represented tape
cells. The caller prefix contributes equally before and after the call. -/
theorem growLeftFinish_storage_le (which : TapeId) (before cells : List (Option Bool))
    (other : Tape) :
    ((growLeftFinish which before cells other).tape which).cells ≤
      ((growLeftStart which before cells other).tape which).cells + 2 := by
  cases which <;> cases cells <;>
    simp [growLeftFinish, growLeftStart, forwardState, onTape, dataTape, pairTape,
      guardedPrefix, Configuration.tape, Tape.cells, encodedCells, encodedCells_length]
  all_goals omega

/-- Polynomial bound for calls satisfying the guarded-region entry
condition. This does not assert `PolynomialTime` on arbitrary standalone
inputs, which are not supplied with that guard. -/
theorem growLeftCell_bound_polynomiallyBounded :
    PolynomiallyBounded (fun m => 17 * m + 14) :=
  ((PolynomiallyBounded.const 17).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 14)

end Machine.VirtualCell
