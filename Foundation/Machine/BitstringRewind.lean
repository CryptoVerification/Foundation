import Foundation.Machine.TapeEquivalence

namespace Machine

/-- Move the input head left across a contiguous block of bit cells, then
right once to its first cell. Every head move and branch is an actual machine
transition. This routine needs a blank immediately left of the block; it
does not locate the beginning of an arbitrary tape containing internal blanks.
The output tape is untouched. -/
def rewindBitstring : Program :=
  [.moveLeft .input, .branch .input 2 0 0, .moveRight .input, .halt]

private def rewindState (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { inputTape := { left := left.map some, current := current, right := right },
    outputTape := output }

private def rewindFinish (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 3,
    inputTape := ({
      current := none
      right := left.reverse.map some ++ current :: right } : Tape).moveRight,
    outputTape := output,
    halted := true }

private theorem rewind_run (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    RunsFor rewindBitstring (rewindState output left current right)
      (rewindFinish output left current right) (2 * left.length + 4) := by
  induction left generalizing current right with
  | nil =>
      let start := rewindState output [] current right
      let moved : Configuration :=
        { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let selected : Configuration := { moved with pc := 2 }
      let restored : Configuration :=
        { selected with pc := 3, inputTape := selected.inputTape.moveRight }
      have hMove : Step rewindBitstring start moved := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          rewindState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBranch : Step rewindBitstring moved selected := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, rewindState, Tape.moveLeft, Instruction.next,
          Configuration.tape]
      have hRestore : Step rewindBitstring selected restored := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, restored, rewindState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hHalt : Step rewindBitstring restored
          (rewindFinish output [] current right) := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, restored, rewindState, rewindFinish, Instruction.next,
          Tape.moveLeft, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hMove) hBranch) hRestore) hHalt
  | cons bit rest ih =>
      let start := rewindState output (bit :: rest) current right
      let moved : Configuration :=
        { start with pc := 1, inputTape := start.inputTape.moveLeft }
      have hMove : Step rewindBitstring start moved := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          rewindState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBranch : Step rewindBitstring moved
          (rewindState output rest (some bit) (current :: right)) := by
        cases bit <;> simp [Step, successors, next, rewindBitstring,
          start, moved, rewindState, Tape.moveLeft, Instruction.next,
          Configuration.tape]
      have hFinish : rewindFinish output rest (some bit) (current :: right) =
          rewindFinish output (bit :: rest) current right := by
        simp [rewindFinish, List.reverse_cons, List.map_append, List.append_assoc]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hMove)
        hBranch).trans (ih (some bit) (current :: right))
      rw [hFinish] at run
      convert run using 1
      simp [List.length_cons]
      omega

/-- Contextual rewind from a known bit block, with arbitrary cells beyond
its current head. Those cells are preserved, including a caller delimiter
and data following it. This is the same charged head scan as the standalone
routine; no tape normalization is performed. -/
theorem rewindBitstring_runs_from (bits : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    RunsFor rewindBitstring
      ({
        inputTape := { left := bits.reverse.map some, current := current, right := right }
        outputTape := output } : Configuration)
      ({
        pc := 3
        inputTape := ({ right := bits.map some ++ current :: right } : Tape).moveRight,
        outputTape := output,
        halted := true } : Configuration)
      (2 * bits.length + 4) := by
  simpa [rewindState, rewindFinish] using rewind_run output bits.reverse current right

/-- Caller state just past a contiguous input bitstring. The caller's output
tape may contain arbitrary data, which this routine preserves exactly. -/
def rewindBitstringStart (bits : List Bool) (output : Tape) : Configuration :=
  { inputTape := { left := bits.reverse.map some }, outputTape := output }

/-- Exact returned tape representation. Its extra outer blanks are not
removed by a free normalization operation. -/
def rewindBitstringFinish (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 3,
    inputTape := ({ right := bits.map some ++ [none] } : Tape).moveRight,
    outputTape := output,
    halted := true }

theorem rewindBitstring_runs (bits : List Bool) (output : Tape) :
    RunsFor rewindBitstring (rewindBitstringStart bits output)
      (rewindBitstringFinish bits output) (2 * bits.length + 4) := by
  simpa [rewindBitstringStart, rewindBitstringFinish, rewindState, rewindFinish]
    using rewind_run output bits.reverse none []

private theorem getD_append_blank (bits : List Bool) (i : Nat) :
    (bits.map some ++ [none]).getD i none = (bits.map some).getD i none := by
  induction bits generalizing i with
  | nil => cases i <;> simp
  | cons bit rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.map_cons, List.cons_append, List.getD_cons_succ]
            using ih i

/-- Rewinding positions the head at the original first bit. Equality is of
tape cells, since scanning beyond the left boundary can store an outer blank.
The routine does not erase or alter any bit. -/
theorem rewindBitstringFinish_input_equivalent (bits : List Bool) (output : Tape) :
    (rewindBitstringFinish bits output).inputTape.Equivalent (Tape.ofBits bits) := by
  cases bits with
  | nil =>
      refine ⟨rfl, ?_, fun _ => rfl⟩
      intro i
      cases i <;> simp [rewindBitstringFinish, Tape.moveRight, Tape.ofBits]
  | cons bit rest =>
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        cases i <;> simp [rewindBitstringFinish, Tape.moveRight, Tape.ofBits]
      · intro i
        simpa [rewindBitstringFinish, Tape.moveRight, Tape.ofBits] using
          getD_append_blank rest i

theorem rewindBitstringFinish_output (bits : List Bool) (output : Tape) :
    (rewindBitstringFinish bits output).outputTape = output := rfl

theorem rewindBitstring_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ rewindBitstring := by simp [rewindBitstring]

/-- Exact distribution from the caller state; the proof uses the charged
operational trace and the absence of random instructions. -/
theorem rewindBitstring_eval (bits : List Bool) (output : Tape) :
    evalConfigWithin rewindBitstring (rewindBitstringStart bits output)
      (2 * bits.length + 4) = PMF.pure (rewindBitstringFinish bits output) :=
  (rewindBitstring_runs bits output).evalConfigWithin_eq_pure_of_no_randomBit
    rewindBitstring_no_randomBit

/-- Every operational branch from the caller state has halted at the bound.
The start need not be the machine's standalone input-loading state. -/
theorem rewindBitstring_halts (bits : List Bool) (output : Tape)
    (finish : Configuration)
    (run : PaddedRunsFor rewindBitstring (rewindBitstringStart bits output)
      finish (2 * bits.length + 4)) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff rewindBitstring
    (rewindBitstringStart bits output) finish (2 * bits.length + 4)).mpr run
  rw [rewindBitstring_eval] at hMem
  have hEq : finish = rewindBitstringFinish bits output := by simpa using hMem
  rw [hEq]
  rfl

private def scratchRewindState (before : List (Option Bool)) (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { inputTape := { left := left.map some ++ none :: before, current := current, right := right },
    outputTape := output }

private def scratchRewindFinish (before : List (Option Bool)) (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 3,
    inputTape := ({
      left := before
      current := none
      right := left.reverse.map some ++ current :: right } : Tape).moveRight,
    outputTape := output,
    halted := true }

private theorem scratch_rewind_run (before : List (Option Bool)) (output : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    RunsFor rewindBitstring (scratchRewindState before output left current right)
      (scratchRewindFinish before output left current right) (2 * left.length + 4) := by
  induction left generalizing current right with
  | nil =>
      let start := scratchRewindState before output [] current right
      let moved : Configuration :=
        { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let selected : Configuration := { moved with pc := 2 }
      let restored : Configuration :=
        { selected with pc := 3, inputTape := selected.inputTape.moveRight }
      have hMove : Step rewindBitstring start moved := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          scratchRewindState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBranch : Step rewindBitstring moved selected := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, scratchRewindState, Tape.moveLeft, Instruction.next,
          Configuration.tape]
      have hRestore : Step rewindBitstring selected restored := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, restored, scratchRewindState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hHalt : Step rewindBitstring restored
          (scratchRewindFinish before output [] current right) := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          selected, restored, scratchRewindState, scratchRewindFinish, Instruction.next,
          Tape.moveLeft, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hMove) hBranch) hRestore) hHalt
  | cons bit rest ih =>
      let start := scratchRewindState before output (bit :: rest) current right
      let moved : Configuration :=
        { start with pc := 1, inputTape := start.inputTape.moveLeft }
      have hMove : Step rewindBitstring start moved := by
        simp [Step, successors, next, rewindBitstring, start, moved,
          scratchRewindState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hBranch : Step rewindBitstring moved
          (scratchRewindState before output rest (some bit) (current :: right)) := by
        cases bit <;> simp [Step, successors, next, rewindBitstring,
          start, moved, scratchRewindState, Tape.moveLeft, Instruction.next,
          Configuration.tape]
      have hFinish : scratchRewindFinish before output rest (some bit) (current :: right) =
          scratchRewindFinish before output (bit :: rest) current right := by
        simp [scratchRewindFinish, List.reverse_cons, List.map_append, List.append_assoc]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hMove)
        hBranch).trans (ih (some bit) (current :: right))
      rw [hFinish] at run
      convert run using 1
      simp [List.length_cons]
      omega


/-- Contextual rewind with a reserved blank behind the scanned block and
arbitrary following cells. Saved caller data beyond the blank and the
entire other tape are preserved by the same native four-instruction scan. -/
theorem rewindScratch_runs_from (before : List (Option Bool)) (bits : List Bool)
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    RunsFor rewindBitstring
      ({
        inputTape := { left := bits.reverse.map some ++ none :: before, current := current, right := right }
        outputTape := output } : Configuration)
      ({
        pc := 3
        inputTape := ({ left := before, right := bits.map some ++ current :: right } : Tape).moveRight
        outputTape := output
        halted := true } : Configuration)
      (2 * bits.length + 4) := by
  simpa [scratchRewindState, scratchRewindFinish] using
    scratch_rewind_run before output bits.reverse current right

/-- Rewind a scratch string whose reserved blank separator precedes saved
caller data. The separator is inspected; the data beyond it are untouched.
The same four finite instructions as `rewindBitstring` perform every move. -/
def rewindScratchStart (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) : Configuration :=
  scratchRewindState before output bits.reverse none []

def rewindScratchFinish (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) : Configuration :=
  { pc := 3,
    inputTape := ({ left := before, right := bits.map some ++ [none] } : Tape).moveRight,
    outputTape := output,
    halted := true }

theorem rewindScratch_runs (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) :
    RunsFor rewindBitstring (rewindScratchStart before bits output)
      (rewindScratchFinish before bits output) (2 * bits.length + 4) := by
  simpa [rewindScratchStart, rewindScratchFinish, scratchRewindFinish] using
    scratch_rewind_run before output bits.reverse none []

theorem rewindBitstring_control_closed (c d : Configuration)
    (hPc : c.pc < rewindBitstring.length) (step : Step rewindBitstring c d)
    (_hRunning : d.halted = false) : d.pc < rewindBitstring.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 4 at hPc
  change d.pc < 4
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, rewindBitstring,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem rewindScratch_eval (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) :
    evalConfigWithin rewindBitstring (rewindScratchStart before bits output)
      (2 * bits.length + 4) = PMF.pure (rewindScratchFinish before bits output) :=
  (rewindScratch_runs before bits output).evalConfigWithin_eq_pure_of_no_randomBit
    rewindBitstring_no_randomBit

private theorem bitCells_prefix (cells : List (Option Bool)) :
    (∃ bits : List Bool, cells = bits.map some) ∨
      (∃ (bits : List Bool) (saved : List (Option Bool)),
        cells = bits.map some ++ none :: saved) := by
  induction cells with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons cell rest ih =>
      cases cell with
      | none => exact Or.inr ⟨[], rest, rfl⟩
      | some bit =>
          rcases ih with ⟨bits, h⟩ | ⟨bits, saved, h⟩
          · exact Or.inl ⟨bit :: bits, by simp [h]⟩
          · exact Or.inr ⟨bit :: bits, saved, by simp [h]⟩

/-- Runtime safety of the native rewind on arbitrary finite caller tapes.
Internal blanks may stop the scan before the intended protocol boundary;
this theorem asserts termination and preservation of the other tape, not
successful recovery of a malformed protocol field. No contiguous-block
or reserved-separator hypothesis is needed for the stopping bound. -/
theorem rewindBitstring_terminates_from (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 2 * input.left.length + 4 ∧
      RunsFor rewindBitstring ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  rcases input with ⟨left, current, right⟩
  rcases bitCells_prefix left with ⟨bits, hLeft⟩ | ⟨bits, saved, hLeft⟩
  · refine ⟨rewindFinish output bits current right, 2 * bits.length + 4, ?_, ?_, rfl, rfl⟩
    · simp [hLeft]
    · simpa only [rewindState, hLeft] using rewind_run output bits current right
  · refine ⟨scratchRewindFinish saved output bits current right, 2 * bits.length + 4, ?_, ?_, rfl, rfl⟩
    · simp only [hLeft, List.length_append, List.length_map, List.length_cons]
      omega
    · simpa only [scratchRewindState, hLeft] using scratch_rewind_run saved output bits current right

/-- Every branch of an invocation on arbitrary finite tapes has halted at
the displayed bound. This is usable after malformed parser outcomes where
the exact successful rewind layout is unavailable. -/
theorem rewindBitstring_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor rewindBitstring
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (2 * input.left.length + 4)) : finish.halted = true := by
  obtain ⟨target, used, hBound, hRun, hHalted, _hOutput⟩ :=
    rewindBitstring_terminates_from input output
  have hEval := hRun.evalConfigWithin_eq_pure_of_no_randomBit rewindBitstring_no_randomBit
  have hAll (c : Configuration) (hc : PaddedRunsFor rewindBitstring
      ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval] at hMem
    have hEq : c = target := by simpa using hMem
    simpa only [hEq] using hHalted
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAll, hEval] at hMem
  have hEq : finish = target := by simpa using hMem
  simpa only [hEq] using hHalted

/-- Exact location of the first bit after the nearest blank to the left.
The returned block is contiguous and the caller's current/right cells are
retained after it. This characterization is valid on arbitrary finite
left prefixes, including prefixes with internal blank separators. -/
theorem rewindBitstring_terminates_with_layout (input output : Tape) :
    ∃ (finish : Configuration) (bits : List Bool) (before : List (Option Bool)),
      bits.length ≤ input.left.length ∧
      RunsFor rewindBitstring ({ inputTape := input, outputTape := output } : Configuration)
        finish (2 * bits.length + 4) ∧ finish.halted = true ∧
      finish.inputTape = { ({ right := bits.map some ++ input.current :: input.right } : Tape).moveRight
        with left := [none] ++ before } ∧ finish.outputTape = output := by
  rcases input with ⟨left, current, right⟩
  rcases bitCells_prefix left with ⟨bits, hLeft⟩ | ⟨bits, saved, hLeft⟩
  · refine ⟨rewindFinish output bits current right, bits.reverse, [], ?_, ?_, rfl, ?_, rfl⟩
    · simp [hLeft]
    · simpa only [rewindState, hLeft, List.length_reverse] using rewind_run output bits current right
    · cases hBits : bits.reverse <;> simp [rewindFinish, hBits, Tape.moveRight]
  · refine ⟨scratchRewindFinish saved output bits current right, bits.reverse, saved, ?_, ?_, rfl, ?_, rfl⟩
    · simp only [List.length_reverse, hLeft, List.length_append, List.length_map, List.length_cons]
      omega
    · simpa only [scratchRewindState, hLeft, List.length_reverse] using scratch_rewind_run saved output bits current right
    · cases hBits : bits.reverse <;> simp [scratchRewindFinish, hBits, Tape.moveRight]

private theorem rewind_suffix_equivalent (bits rest : List Bool) (saved : List (Option Bool)) :
    ({ ({ right := bits.map some ++ (Tape.ofBits rest).current :: (Tape.ofBits rest).right } : Tape).moveRight
      with left := [none] ++ saved } : Tape).Equivalent
        { Tape.ofBits (bits ++ rest) with left := [none] ++ saved } := by
  cases bits with
  | nil => cases rest <;> exact Tape.Equivalent.refl _
  | cons bit tail =>
      cases rest with
      | nil =>
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro i
          simpa only [Tape.ofBits, List.append_nil, List.map_cons, List.cons_append, Tape.moveRight] using getD_append_blank tail i
      | cons next remaining =>
          simp only [List.cons_append, List.map_cons, List.map_append, Tape.ofBits, Tape.moveRight]
          exact Tape.Equivalent.refl _

/-- Rewinding before a contiguous suffix, including an empty or truncated
suffix, exposes another contiguous bitstring. An outer represented blank
may remain, so the assertion compares physical cells rather than records.
The arbitrary caller data before the nearest blank are retained. -/
theorem rewindBitstring_terminates_from_suffix (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    ∃ (finish : Configuration) (leading : List Bool) (saved : List (Option Bool)),
      leading.length ≤ before.length ∧
      RunsFor rewindBitstring
        ({ inputTape := { Tape.ofBits rest with left := before }, outputTape := output } : Configuration)
        finish (2 * leading.length + 4) ∧ finish.halted = true ∧
      finish.inputTape.Equivalent { Tape.ofBits (leading ++ rest) with left := [none] ++ saved } ∧
      finish.outputTape = output := by
  obtain ⟨finish, leading, saved, hLength, hRun, hHalted, hInput, hOutput⟩ :=
    rewindBitstring_terminates_with_layout ({ Tape.ofBits rest with left := before } : Tape) output
  refine ⟨finish, leading, saved, hLength, hRun, hHalted, ?_, hOutput⟩
  rw [hInput]
  exact rewind_suffix_equivalent leading rest saved

end Machine
