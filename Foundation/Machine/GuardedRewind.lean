import Foundation.Machine.GuardedInput

namespace Machine.GuardedCompiler

open VirtualCell

/-- Rewind a guarded region to its first logical pair. Words `1b` are data,
`00` is a logical blank, and `01` is the boundary. Each physical head move
and branch is counted. The other tape and cells outside the guard are never
changed. Correctness requires an already valid guarded representation. -/
def rewindRegion (which : TapeId) : Program :=
  [.moveLeft which, .moveLeft which, .branch which 9 3 0,
   .moveRight which, .branch which 9 5 7,
   .moveLeft which, .jump 0, .moveRight which, .halt, .halt]

/-- Mathematical head-position postcondition, not a tape-normalization
opcode. All logical cells retain their left-to-right order. -/
def rewoundTape (source : Tape) : Tape :=
  match source.left.reverse ++ source.current :: source.right with
  | [] => {}
  | cell :: rest => { current := cell, right := rest }

def rewindRegionSteps : List (Option Bool) → Nat
  | [] => 7
  | cell :: rest => (if cell = none then 7 else 3) + rewindRegionSteps rest

def rewindRegionStart (which : TapeId) (before : List (Option Bool))
    (logical other : Tape) : Configuration :=
  match which with
  | .input => start (encodeTape before logical) other
  | .output => start other (encodeTape before logical)

def rewindRegionFinish (which : TapeId) (before : List (Option Bool))
    (logical other : Tape) : Configuration :=
  { rewindRegionStart which before (rewoundTape logical) other with pc := 8, halted := true }

private theorem rewind_boundary (which : TapeId) (before : List (Option Bool))
    (current : Option Bool) (right : List (Option Bool)) (other : Tape) :
    RunsFor (rewindRegion which)
      (rewindRegionStart which before { current := current, right := right } other)
      (rewindRegionFinish which before { current := current, right := right } other) 7 := by
  let initial := rewindRegionStart which before { current := current, right := right } other
  let first := (initial.updateTape which Tape.moveLeft).advance
  let second := (first.updateTape which Tape.moveLeft).advance
  let selected : Configuration := { second with pc := 3 }
  let inspected := (selected.updateTape which Tape.moveRight).advance
  let ready : Configuration := { inspected with pc := 7 }
  let restored := (ready.updateTape which Tape.moveRight).advance
  have h0 : Step (rewindRegion which) initial first := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first,
      rewindRegionStart, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step (rewindRegion which) first second := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      rewindRegionStart, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step (rewindRegion which) second selected := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      selected, rewindRegionStart, start, Instruction.next, Configuration.updateTape,
      Configuration.advance, Configuration.tape, encodeTape, encodedLeftCells, pairTape, Tape.moveLeft]
  have h3 : Step (rewindRegion which) selected inspected := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      selected, inspected, rewindRegionStart, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h4 : Step (rewindRegion which) inspected ready := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      selected, inspected, ready, rewindRegionStart, start, Instruction.next, Configuration.updateTape,
      Configuration.advance, Configuration.tape, encodeTape, encodedLeftCells, pairTape,
      Tape.moveLeft, Tape.moveRight]
  have h5 : Step (rewindRegion which) ready restored := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      selected, inspected, ready, restored, rewindRegionStart, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step (rewindRegion which) restored
      (rewindRegionFinish which before { current := current, right := right } other) := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      selected, inspected, ready, restored, rewindRegionStart, rewindRegionFinish,
      rewoundTape, start, Instruction.next, Configuration.updateTape, Configuration.advance,
      encodeTape, encodedLeftCells, pairTape, Tape.moveLeft, Tape.moveRight]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6

private theorem rewind_one_cell (which : TapeId) (before : List (Option Bool))
    (previous : Option Bool) (rest : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) (other : Tape) :
    RunsFor (rewindRegion which)
      (rewindRegionStart which before { left := previous :: rest, current := current, right := right } other)
      (rewindRegionStart which before { left := rest, current := previous, right := current :: right } other)
      (if previous = none then 7 else 3) := by
  let initial := rewindRegionStart which before
    { left := previous :: rest, current := current, right := right } other
  let first := (initial.updateTape which Tape.moveLeft).advance
  let second := (first.updateTape which Tape.moveLeft).advance
  let ready := rewindRegionStart which before
    { left := rest, current := previous, right := current :: right } other
  have h0 : Step (rewindRegion which) initial first := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first,
      rewindRegionStart, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h1 : Step (rewindRegion which) first second := by
    cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
      rewindRegionStart, start, Instruction.next, Configuration.updateTape, Configuration.advance]
  cases previous with
  | some bit =>
      have h2 : Step (rewindRegion which) second ready := by
        cases which <;> cases bit <;>
          simp [Step, successors, next, rewindRegion, initial, first, second, ready,
            rewindRegionStart, start, Instruction.next, Configuration.updateTape,
            Configuration.advance, Configuration.tape, encodeTape, encodedLeftCells,
            encodedCells, pairTape, code, Tape.moveLeft]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | none =>
      let selected : Configuration := { second with pc := 3 }
      let inspected := (selected.updateTape which Tape.moveRight).advance
      let back : Configuration := { inspected with pc := 5 }
      let restored := (back.updateTape which Tape.moveLeft).advance
      have h2 : Step (rewindRegion which) second selected := by
        cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
          selected, rewindRegionStart, start, Instruction.next, Configuration.updateTape,
          Configuration.advance, Configuration.tape, encodeTape, encodedLeftCells, pairTape, code, Tape.moveLeft]
      have h3 : Step (rewindRegion which) selected inspected := by
        cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
          selected, inspected, rewindRegionStart, start, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have h4 : Step (rewindRegion which) inspected back := by
        cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
          selected, inspected, back, rewindRegionStart, start, Instruction.next, Configuration.updateTape,
          Configuration.advance, Configuration.tape, encodeTape, encodedLeftCells, pairTape, code,
          Tape.moveLeft, Tape.moveRight]
      have h5 : Step (rewindRegion which) back restored := by
        cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
          selected, inspected, back, restored, rewindRegionStart, start, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have h6 : Step (rewindRegion which) restored ready := by
        cases which <;> simp [Step, successors, next, rewindRegion, initial, first, second,
          selected, inspected, back, restored, ready, rewindRegionStart, start, Instruction.next,
          Configuration.updateTape, Configuration.advance, encodeTape, encodedLeftCells, encodedCells,
          pairTape, code, Tape.moveLeft, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6

theorem rewindRegion_runs (which : TapeId) (before : List (Option Bool)) (logical other : Tape) :
    RunsFor (rewindRegion which) (rewindRegionStart which before logical other)
      (rewindRegionFinish which before logical other) (rewindRegionSteps logical.left) := by
  cases logical with
  | mk left current right =>
      induction left generalizing current right with
      | nil => exact rewind_boundary which before current right other
      | cons previous rest ih =>
          have run := (rewind_one_cell which before previous rest current right other).trans
            (ih previous (current :: right))
          have hFinish : rewindRegionFinish which before
              { left := rest, current := previous, right := current :: right } other =
              rewindRegionFinish which before
                { left := previous :: rest, current := current, right := right } other := by
            simp [rewindRegionFinish, rewoundTape, List.reverse_cons, List.append_assoc]
          rw [hFinish] at run
          exact run

theorem rewindRegionSteps_le (left : List (Option Bool)) :
    rewindRegionSteps left ≤ 7 * left.length + 7 := by
  induction left with
  | nil => rfl
  | cons cell rest ih =>
      simp only [rewindRegionSteps, List.length_cons]
      split <;> omega

theorem rewindRegion_no_randomBit (which tape : TapeId) :
    Instruction.randomBit tape ∉ rewindRegion which := by simp [rewindRegion]

theorem rewindRegion_eval (which : TapeId) (before : List (Option Bool)) (logical other : Tape) :
    evalConfigWithin (rewindRegion which) (rewindRegionStart which before logical other)
      (rewindRegionSteps logical.left) = PMF.pure (rewindRegionFinish which before logical other) :=
  (rewindRegion_runs which before logical other).evalConfigWithin_eq_pure_of_no_randomBit
    (rewindRegion_no_randomBit which)

theorem rewindRegion_control_closed (which : TapeId) (c d : Configuration)
    (hPc : c.pc < (rewindRegion which).length) (step : Step (rewindRegion which) c d)
    (_hRunning : d.halted = false) : d.pc < (rewindRegion which).length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 10 at hPc
  interval_cases hIndex : c.pc <;>
    cases hCell : (c.tape which).current with
    | none =>
        simp [Step, successors, next, hActive, hIndex, rewindRegion,
          Instruction.next, hCell] at step
        subst d
        cases which <;> simp [rewindRegion, Configuration.advance, Configuration.updateTape, hIndex]
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, hActive, hIndex, rewindRegion,
            Instruction.next, hCell] at step <;>
          subst d <;>
          cases which <;> simp [rewindRegion, Configuration.advance, Configuration.updateTape, hIndex]

theorem rewindRegion_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (which : TapeId) (before : List (Option Bool)) (logical other : Tape) :
    evalConfigWithin (Program.withSubroutine pre (rewindRegion which) suffix returnPc)
      ((rewindRegionStart which before logical other).rebasePc pre.length)
      (rewindRegionSteps logical.left) =
      PMF.pure ((rewindRegionFinish which before logical other).resumeAt returnPc) :=
  (rewindRegion_runs which before logical other).evalConfigWithin_withSubroutine_halted_of_closed
    pre (rewindRegion which) suffix returnPc
    (by cases which <;> simp [rewindRegionStart, start, rewindRegion])
    (by cases which <;> rfl) rfl (rewindRegion_control_closed which)
    (rewindRegion_no_randomBit which)

theorem rewindRegionSteps_bits (bits : List Bool) :
    rewindRegionSteps (bits.map some) = 3 * bits.length + 7 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [rewindRegionSteps, ih, Nat.mul_add, Nat.add_comm, Nat.add_assoc]

/-- The logical input includes its materialized trailing blank. This is a
postcondition; no outer blank is silently erased or normalized. -/
def packedLogicalInput (input : List Bool) : Tape :=
  rewoundTape { left := input.reverse.map some }

/-- Actual code composition: packing returns to the rewind routine, which
returns to an explicit final halt. Each absolute address is rebased. -/
def packAndRewind : Program :=
  packInput.asSubroutine 0 23 ++ (rewindRegion .output).asSubroutine 23 34 ++ [.halt]

def packAndRewindFinish (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) : Configuration :=
  { pc := 34,
    inputTape := { left := input.reverse.map some ++ beforeInput },
    outputTape := encodeTape beforeOutput (packedLogicalInput input),
    halted := true }

/-- Packing and returning to the first pair costs exactly `10*m + 18`
transitions, including both call-return jumps and the final halt. -/
theorem packAndRewind_runs (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    RunsFor packAndRewind (packInputStart beforeInput beforeOutput input)
      (packAndRewindFinish beforeInput beforeOutput input) (10 * input.length + 18) := by
  have hPack := (packInput_runs beforeInput beforeOutput input).withSubroutine_halted_of_closed
    [] packInput ((rewindRegion .output).asSubroutine 23 34 ++ [.halt]) 23
    (by simp [packInputStart, packInput]) rfl rfl packInput_control_closed
  change RunsFor packAndRewind (packInputStart beforeInput beforeOutput input)
    ((packInputFinish beforeInput beforeOutput input).resumeAt 23) (7 * input.length + 10) at hPack
  have hRewind := (rewindRegion_runs .output beforeOutput { left := input.reverse.map some }
      { left := input.reverse.map some ++ beforeInput }).withSubroutine_halted_of_closed
    (packInput.asSubroutine 0 23) (rewindRegion .output) [.halt] 34
    (by simp [rewindRegionStart, start, rewindRegion]) rfl rfl (rewindRegion_control_closed .output)
  change RunsFor packAndRewind ((packInputFinish beforeInput beforeOutput input).resumeAt 23)
    ((packAndRewindFinish beforeInput beforeOutput input).resumeAt 34)
    (rewindRegionSteps (input.reverse.map some)) at hRewind
  rw [rewindRegionSteps_bits, List.length_reverse] at hRewind
  have hHalt : Step packAndRewind
      ((packAndRewindFinish beforeInput beforeOutput input).resumeAt 34)
      (packAndRewindFinish beforeInput beforeOutput input) := by
    simp [Step, successors, next, packAndRewind, Program.asSubroutine, packInput, rewindRegion,
      packAndRewindFinish, Configuration.resumeAt, Instruction.asSubroutine, Instruction.next]
  convert RunsFor.succ (hPack.trans hRewind) hHalt using 1; omega

theorem packAndRewind_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ packAndRewind := by
  simp [packAndRewind, Program.asSubroutine, packInput, rewindRegion, Instruction.asSubroutine]

theorem packAndRewind_eval (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin packAndRewind (packInputStart beforeInput beforeOutput input)
      (10 * input.length + 18) = PMF.pure (packAndRewindFinish beforeInput beforeOutput input) :=
  (packAndRewind_runs beforeInput beforeOutput input).evalConfigWithin_eq_pure_of_no_randomBit
    packAndRewind_no_randomBit

theorem packAndRewind_haltsWithin (input : List Bool) :
    HaltsWithin packAndRewind input (10 * input.length + 18) := by
  intro final run
  have hInitial : packInputStart [] [] input = Configuration.initial input := by cases input <;> rfl
  rw [← hInitial] at run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [packAndRewind_eval] at hMem
  have hFinal : final = packAndRewindFinish [] [] input := by simpa using hMem
  subst final
  rfl

theorem packAndRewind_polynomialTime : PolynomialTime packAndRewind := by
  refine ⟨fun m => 10 * m + 18, ?_, packAndRewind_haltsWithin⟩
  exact ((PolynomiallyBounded.const 10).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 18)

end Machine.GuardedCompiler
