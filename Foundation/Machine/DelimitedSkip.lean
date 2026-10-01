import Foundation.Machine.Encoding
import Foundation.Machine.SubroutineProbability

namespace Machine

/-- Skip one escaped-bit field by native reads and head moves. A true marker
is followed by its data cell, and false ends the field. No payload is copied
or decoded. The other tape and caller data beyond the field are untouched. -/
def skipDelimited : Program :=
  [.branch .input 6 4 1, .moveRight .input, .moveRight .input, .jump 0,
    .moveRight .input, .halt, .halt]

/-- Even a malformed escaped field only advances the input head. The cells
remaining to its right are a suffix of the actual original finite tape. -/
private theorem skipDelimited_step_input_moveRight (c d : Configuration)
    (step : Step skipDelimited c d) :
    d.inputTape = c.inputTape ∨ d.inputTape = c.inputTape.moveRight := by
  have hActive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) step)
  by_cases hPc : c.pc < 7
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, skipDelimited,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
  · have hNone : skipDelimited[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 7 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

/-- The remaining input cells form an actual suffix, including blanks. -/
theorem skipDelimited_input_right_suffix {start finish : Configuration} {used : Nat}
    (run : RunsFor skipDelimited start finish used) :
    ∃ count, finish.inputTape.right = start.inputTape.right.drop count :=
  run.input_right_suffix_of_step (fun c d step => by
    rcases skipDelimited_step_input_moveRight c d step with hSame | hRight
    · exact Or.inl (congrArg Tape.right hSame)
    · apply Or.inr
      rw [hRight]
      cases hCells : c.inputTape.right <;> simp [Tape.moveRight, hCells])

/-- Escaped-field reading retains the whole input tape and advances its
head only by charged one-cell moves, even on a malformed field. -/
theorem skipDelimited_input_moveRight {start finish : Configuration} {used : Nat}
    (run : RunsFor skipDelimited start finish used) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape :=
  run.input_moveRight_of_step skipDelimited_step_input_moveRight

private def delimitedCells (before cells : List (Option Bool)) : Tape :=
  match cells with
  | [] => { left := before }
  | cell :: rest => { left := before, current := cell, right := rest }

def skipDelimitedStart (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := delimitedCells before ((FiniteBitEncoding.delimit field).map some ++ tail),
    outputTape := output }

def skipDelimitedFinish (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 5,
    inputTape := delimitedCells ((FiniteBitEncoding.delimit field).reverse.map some ++ before) tail,
    outputTape := output, halted := true }

/-- Exactly four transitions per payload bit and three for the terminating
false marker. This counts each read, each move, the loop jump and halt. -/
theorem skipDelimited_runs (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) :
    RunsFor skipDelimited (skipDelimitedStart before field tail output)
      (skipDelimitedFinish before field tail output) (4 * field.length + 3) := by
  induction field generalizing before with
  | nil =>
      let start := skipDelimitedStart before [] tail output
      let selected : Configuration := { start with pc := 4 }
      let moved : Configuration := { selected with pc := 5, inputTape := selected.inputTape.moveRight }
      have h0 : Step skipDelimited start selected := by
        simp [Step, successors, next, skipDelimited, start, selected,
          skipDelimitedStart, delimitedCells, FiniteBitEncoding.delimit,
          Instruction.next, Configuration.tape]
      have h1 : Step skipDelimited selected moved := by
        simp [Step, successors, next, skipDelimited, start, selected, moved,
          skipDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipDelimited moved (skipDelimitedFinish before [] tail output) := by
        cases tail <;> simp [Step, successors, next, skipDelimited, start, selected, moved,
          skipDelimitedStart, skipDelimitedFinish, delimitedCells, FiniteBitEncoding.delimit,
          Tape.moveRight, Instruction.next]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | cons bit rest ih =>
      let start := skipDelimitedStart before (bit :: rest) tail output
      let selected : Configuration := { start with pc := 1 }
      let moved : Configuration := { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      let advanced : Configuration := { moved with pc := 3, inputTape := moved.inputTape.moveRight }
      have h0 : Step skipDelimited start selected := by
        simp [Step, successors, next, skipDelimited, start, selected,
          skipDelimitedStart, delimitedCells, FiniteBitEncoding.delimit,
          Instruction.next, Configuration.tape]
      have h1 : Step skipDelimited selected moved := by
        simp [Step, successors, next, skipDelimited, start, selected, moved,
          skipDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step skipDelimited moved advanced := by
        simp [Step, successors, next, skipDelimited, start, selected, moved, advanced,
          skipDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h3 : Step skipDelimited advanced
          (skipDelimitedStart (some bit :: some true :: before) rest tail output) := by
        cases rest <;> simp [Step, successors, next, skipDelimited, start, selected, moved,
          advanced, skipDelimitedStart, delimitedCells, FiniteBitEncoding.delimit,
          Instruction.next, Tape.moveRight]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3).trans
          (ih (some bit :: some true :: before))
      have hFinish : skipDelimitedFinish (some bit :: some true :: before) rest tail output =
          skipDelimitedFinish before (bit :: rest) tail output := by
        simp [skipDelimitedFinish, FiniteBitEncoding.delimit, List.reverse_cons,
          List.map_append, List.append_assoc]
      rw [hFinish] at run
      convert run using 1
      simp only [List.length_cons]
      omega

theorem skipDelimited_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ skipDelimited := by simp [skipDelimited]

theorem skipDelimited_eval (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) :
    evalConfigWithin skipDelimited (skipDelimitedStart before field tail output)
      (4 * field.length + 3) = PMF.pure (skipDelimitedFinish before field tail output) :=
  (skipDelimited_runs before field tail output).evalConfigWithin_eq_pure_of_no_randomBit
    skipDelimited_no_randomBit

theorem skipDelimited_control_closed (c d : Configuration)
    (hPc : c.pc < skipDelimited.length) (step : Step skipDelimited c d)
    (_hRunning : d.halted = false) : d.pc < skipDelimited.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 7 at hPc
  change d.pc < 7
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, skipDelimited,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem skipDelimitedStart_layout (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) :
    skipDelimitedStart before field tail output =
      { inputTape := { ({ right := (FiniteBitEncoding.delimit field).map some ++ tail } : Tape).moveRight
          with left := before }, outputTape := output } := by
  cases field <;> simp [skipDelimitedStart, delimitedCells, FiniteBitEncoding.delimit, Tape.moveRight]

theorem skipDelimitedFinish_layout (before : List (Option Bool)) (field : List Bool)
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    skipDelimitedFinish before field (current :: right) output =
      { pc := 5,
        inputTape := {
          left := (FiniteBitEncoding.delimit field).reverse.map some ++ before
          current := current
          right := right },
        outputTape := output, halted := true } := rfl

/-- Full contextual layout, including an empty remaining tail. The head is
at the first remaining cell, and the consumed delimiter stays in the prefix. -/
theorem skipDelimitedFinish_layout_cells (before : List (Option Bool)) (field : List Bool)
    (tail : List (Option Bool)) (output : Tape) :
    skipDelimitedFinish before field tail output =
      { pc := 5, inputTape := { ({ right := tail } : Tape).moveRight with
          left := (FiniteBitEncoding.delimit field).reverse.map some ++ before },
        outputTape := output, halted := true } := by
  cases tail <;> rfl

private theorem skipDelimited_blank_runs (input output : Tape) (hBlank : input.current = none) :
    RunsFor skipDelimited ({ inputTape := input, outputTape := output } : Configuration)
      { pc := 6, inputTape := input, outputTape := output, halted := true } 2 := by
  let selected : Configuration := { pc := 6, inputTape := input, outputTape := output }
  have h0 : Step skipDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, skipDelimited, selected, Instruction.next, Configuration.tape, hBlank]
  have h1 : Step skipDelimited selected { selected with halted := true } := by
    simp [Step, successors, next, skipDelimited, selected, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1

private theorem skipDelimited_true_prefix_runs (input output : Tape) (hTrue : input.current = some true) :
    RunsFor skipDelimited ({ inputTape := input, outputTape := output } : Configuration)
      { inputTape := input.moveRight.moveRight, outputTape := output } 4 := by
  let selected : Configuration := { pc := 1, inputTape := input, outputTape := output }
  let moved : Configuration := { pc := 2, inputTape := input.moveRight, outputTape := output }
  let advanced : Configuration := { pc := 3, inputTape := input.moveRight.moveRight, outputTape := output }
  have h0 : Step skipDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, skipDelimited, selected, Instruction.next, Configuration.tape, hTrue]
  have h1 : Step skipDelimited selected moved := by
    simp [Step, successors, next, skipDelimited, selected, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step skipDelimited moved advanced := by
    simp [Step, successors, next, skipDelimited, moved, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step skipDelimited advanced
      ({ inputTape := input.moveRight.moveRight, outputTape := output } : Configuration) := by
    simp [Step, successors, next, skipDelimited, advanced, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3

private theorem skipDelimited_finite_cells (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 4 * input.right.length + 7 ∧
      RunsFor skipDelimited ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  cases hCurrent : input.current with
  | none => exact ⟨{ pc := 6, inputTape := input, outputTape := output, halted := true }, 2,
      by omega, skipDelimited_blank_runs input output hCurrent, rfl, rfl⟩
  | some bit =>
      cases bit with
      | false =>
          let selected : Configuration := { pc := 4, inputTape := input, outputTape := output }
          let moved : Configuration := { pc := 5, inputTape := input.moveRight, outputTape := output }
          have h0 : Step skipDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
            simp [Step, successors, next, skipDelimited, selected, Instruction.next, Configuration.tape, hCurrent]
          have h1 : Step skipDelimited selected moved := by
            simp [Step, successors, next, skipDelimited, selected, moved,
              Instruction.next, Configuration.updateTape, Configuration.advance]
          have h2 : Step skipDelimited moved { moved with halted := true } := by
            simp [Step, successors, next, skipDelimited, moved, Instruction.next]
          exact ⟨{ moved with halted := true }, 3, by omega,
            RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2, rfl, rfl⟩
      | true =>
          have hPrefix := skipDelimited_true_prefix_runs input output hCurrent
          cases hRight : input.right with
          | nil =>
              have hBlank : input.moveRight.moveRight.current = none := by simp [Tape.moveRight, hRight]
              exact ⟨{ pc := 6, inputTape := input.moveRight.moveRight, outputTape := output, halted := true },
                6, by omega, hPrefix.trans (skipDelimited_blank_runs _ _ hBlank), rfl, rfl⟩
          | cons cell rest =>
              obtain ⟨finish, used, hBound, hRun, hHalt, hOutput⟩ :=
                skipDelimited_finite_cells input.moveRight.moveRight output
              refine ⟨finish, 4 + used, ?_, hPrefix.trans hRun, hHalt, hOutput⟩
              cases rest <;> simp only [Tape.moveRight, hRight, List.length_cons, List.length_nil] at hBound ⊢ <;> omega
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

/-- Native escaped-field skipping stops on every finite retained tape.
A missing or blank payload is still crossed by the two actual moves of
this program; no decoded-field validity is inferred from termination. -/
theorem skipDelimited_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 4 * input.cells + 7 ∧
      RunsFor skipDelimited ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, hBound, hRun, hHalt, hOutput⟩ := skipDelimited_finite_cells input output
  refine ⟨finish, used, ?_, hRun, hHalt, hOutput⟩
  dsimp only [Tape.cells]
  omega

/-- The deterministic all-tape stopping certificate covers every padded
trace at the displayed common budget, not just the selected actual trace. -/
theorem skipDelimited_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor skipDelimited
      ({ inputTape := input, outputTape := output } : Configuration) finish (4 * input.cells + 7)) :
    finish.halted = true := by
  obtain ⟨target, used, hBound, hRun, hHalt, _hOutput⟩ := skipDelimited_terminates_from_anyTape input output
  have hEval := hRun.evalConfigWithin_eq_pure_of_no_randomBit skipDelimited_no_randomBit
  have hAll (c : Configuration)
      (trace : PaddedRunsFor skipDelimited
        ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hEval] at hMem
    have hEq : c = target := by simpa using hMem
    simpa only [hEq] using hHalt
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAll, hEval] at hMem
  have hEq : finish = target := by simpa using hMem
  simpa only [hEq] using hHalt

end Machine
