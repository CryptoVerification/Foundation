import Foundation.Crypto.Semantics.Machine.ChooseTwoRanges

namespace Machine.ChooseRangeStatusGate

/-- Read the first range decision, scan the preserved second field using
the modulus bits as a width counter, and write their conjunction into the
blank cell immediately preceding the modulus. Both overwritten response
delimiters are restored to false after being read. This is a native status
gate; it does not yet check the two subgroup conditions or produce a
normalized reply. -/
def program : Program :=
  [.branch .input 18 18 1,
   .write .input false,
   .moveRight .input,
   .moveLeft .output,
   .branch .output 9 5 5,
   .moveRight .input,
   .moveRight .input,
   .jump 3,
   .halt,
   .branch .input 10 10 14,
   .write .input false,
   .write .output false,
   .moveRight .output,
   .halt,
   .write .input false,
   .write .output true,
   .moveRight .output,
   .halt,
   .write .input false,
   .moveRight .input,
   .moveLeft .output,
   .branch .output 26 22 22,
   .moveRight .input,
   .moveRight .input,
   .jump 20,
   .halt,
   .write .input false,
   .write .output false,
   .moveRight .output,
   .halt]

def entry (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

def goodLoop (input output : Tape) : Configuration :=
  { pc := 3, inputTape := input, outputTape := output }

def badLoop (input output : Tape) : Configuration :=
  { pc := 20, inputTape := input, outputTape := output }

def goodFinish (input output : Tape) (decision : Bool) : Configuration :=
  { pc := if decision then 17 else 13,
    inputTape := input.write (some false),
    outputTape := (output.moveLeft.write (some decision)).moveRight,
    halted := true }

def badFinish (input output : Tape) : Configuration :=
  { pc := 29, inputTape := input.write (some false),
    outputTape := (output.moveLeft.write (some false)).moveRight,
    halted := true }

theorem enter_good (input output : Tape)
    (h : input.current = some true) :
    evalConfigWithin program (entry input output) 3 =
      PMF.pure (goodLoop (input.write (some false)).moveRight output) := by
  simp [evalConfigWithin, stepPMF, next, program, entry, goodLoop,
    h, Instruction.next, Configuration.advance, Configuration.updateTape,
    Configuration.tape, PMF.pure_bind]

theorem enter_bad (input output : Tape)
    (h : input.current ≠ some true) :
    evalConfigWithin program (entry input output) 3 =
      PMF.pure (badLoop (input.write (some false)).moveRight output) := by
  cases hc : input.current with
  | none =>
      simp [evalConfigWithin, stepPMF, next, program, entry, badLoop,
        hc, Instruction.next, Configuration.advance, Configuration.updateTape,
        Configuration.tape, PMF.pure_bind]
  | some bit =>
      cases bit
      · simp [evalConfigWithin, stepPMF, next, program, entry, badLoop,
          hc, Instruction.next, Configuration.advance, Configuration.updateTape,
          Configuration.tape, PMF.pure_bind]
      · exact (h hc).elim

theorem good_cycle (input output : Tape) (bit : Bool)
    (h : output.moveLeft.current = some bit) :
    evalConfigWithin program (goodLoop input output) 5 =
      PMF.pure (goodLoop input.moveRight.moveRight output.moveLeft) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, goodLoop,
      h, Instruction.next, Configuration.advance, Configuration.updateTape,
      Configuration.tape, PMF.pure_bind]

theorem bad_cycle (input output : Tape) (bit : Bool)
    (h : output.moveLeft.current = some bit) :
    evalConfigWithin program (badLoop input output) 5 =
      PMF.pure (badLoop input.moveRight.moveRight output.moveLeft) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, badLoop,
      h, Instruction.next, Configuration.advance, Configuration.updateTape,
      Configuration.tape, PMF.pure_bind]

theorem good_stop (input output : Tape)
    (h : output.moveLeft.current = none) :
    evalConfigWithin program (goodLoop input output) 7 =
      PMF.pure (goodFinish input output (input.current == some true)) := by
  cases hc : input.current with
  | none =>
      simp [evalConfigWithin, stepPMF, next, program, goodLoop,
        goodFinish, h, hc, Instruction.next, Configuration.advance,
        Configuration.updateTape, Configuration.tape, PMF.pure_bind]
  | some bit =>
      cases bit <;>
        simp [evalConfigWithin, stepPMF, next, program, goodLoop,
          goodFinish, h, hc, Instruction.next, Configuration.advance,
          Configuration.updateTape, Configuration.tape, PMF.pure_bind]

theorem bad_stop (input output : Tape)
    (h : output.moveLeft.current = none) :
    evalConfigWithin program (badLoop input output) 6 =
      PMF.pure (badFinish input output) := by
  simp [evalConfigWithin, stepPMF, next, program, badLoop,
    badFinish, h, Instruction.next, Configuration.advance,
    Configuration.updateTape, Configuration.tape, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, stepPMF, next, h, ih]

/-- Both branches are total on arbitrary finite tapes. The two known
range decisions are needed for correctness, not for termination. -/
theorem good_loop_any (input output : Tape) :
    ∃ final, final.halted = true ∧
      evalConfigWithin program (goodLoop input output)
        (5 * output.left.length + 7) = PMF.pure final := by
  cases hLeft : output.left with
  | nil =>
      refine ⟨goodFinish input output (input.current == some true), rfl, ?_⟩
      simpa [hLeft, Tape.moveLeft] using
        good_stop input output (by simp [Tape.moveLeft, hLeft])
  | cons cell rest =>
      cases cell with
      | none =>
          refine ⟨goodFinish input output (input.current == some true), rfl, ?_⟩
          have hStop := good_stop input output (by simp [Tape.moveLeft, hLeft])
          have hBudget : 5 * output.left.length + 7 =
              7 + 5 * output.left.length := by omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hStop, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | some bit =>
          let nextInput := input.moveRight.moveRight
          let nextOutput := output.moveLeft
          obtain ⟨final, hHalt, hEval⟩ := good_loop_any nextInput nextOutput
          refine ⟨final, hHalt, ?_⟩
          have hCycle := good_cycle input output bit
            (by simp [Tape.moveLeft, hLeft])
          have hLength : nextOutput.left.length = rest.length := by
            simp [nextOutput, Tape.moveLeft, hLeft]
          have hBudget : 5 * output.left.length + 7 =
              5 + (5 * nextOutput.left.length + 7) := by
            simp only [hLeft, List.length_cons, hLength]
            omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hCycle, PMF.pure_bind]
          exact hEval
termination_by output.left.length
decreasing_by simp [nextOutput, Tape.moveLeft, hLeft]

theorem bad_loop_any (input output : Tape) :
    ∃ final, final.halted = true ∧
      evalConfigWithin program (badLoop input output)
        (5 * output.left.length + 6) = PMF.pure final := by
  cases hLeft : output.left with
  | nil =>
      refine ⟨badFinish input output, rfl, ?_⟩
      simpa [hLeft, Tape.moveLeft] using
        bad_stop input output (by simp [Tape.moveLeft, hLeft])
  | cons cell rest =>
      cases cell with
      | none =>
          refine ⟨badFinish input output, rfl, ?_⟩
          have hStop := bad_stop input output (by simp [Tape.moveLeft, hLeft])
          have hBudget : 5 * output.left.length + 6 =
              6 + 5 * output.left.length := by omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hStop, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | some bit =>
          let nextInput := input.moveRight.moveRight
          let nextOutput := output.moveLeft
          obtain ⟨final, hHalt, hEval⟩ := bad_loop_any nextInput nextOutput
          refine ⟨final, hHalt, ?_⟩
          have hCycle := bad_cycle input output bit
            (by simp [Tape.moveLeft, hLeft])
          have hLength : nextOutput.left.length = rest.length := by
            simp [nextOutput, Tape.moveLeft, hLeft]
          have hBudget : 5 * output.left.length + 6 =
              5 + (5 * nextOutput.left.length + 6) := by
            simp only [hLeft, List.length_cons, hLength]
            omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hCycle, PMF.pure_bind]
          exact hEval
termination_by output.left.length
decreasing_by simp [nextOutput, Tape.moveLeft, hLeft]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem runs_any (input output : Tape) :
    ∃ final used, used ≤ 5 * output.left.length + 10 ∧
      RunsFor program (entry input output) final used ∧
      final.halted = true := by
  by_cases hFirst : input.current = some true
  · obtain ⟨final, hHalt, hLoop⟩ := good_loop_any (input.write (some false)).moveRight output
    have hFull : evalConfigWithin program (entry input output)
        (5 * output.left.length + 10) = PMF.pure final := by
      have hBudget : 5 * output.left.length + 10 =
          3 + (5 * output.left.length + 7) := by omega
      rw [hBudget, evalConfigWithin_add, enter_good input output hFirst,
        PMF.pure_bind]
      exact hLoop
    have hSupport : final ∈
        (evalConfigWithin program (entry input output)
          (5 * output.left.length + 10)).support := by
      rw [hFull]
      simp
    obtain ⟨used, hUsed, run⟩ :=
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
    exact ⟨final, used, hUsed, run, hHalt⟩
  · obtain ⟨final, hHalt, hLoop⟩ := bad_loop_any (input.write (some false)).moveRight output
    have hFull : evalConfigWithin program (entry input output)
        (5 * output.left.length + 10) = PMF.pure final := by
      have hBudget : 5 * output.left.length + 10 =
          (3 + (5 * output.left.length + 6)) + 1 := by omega
      rw [hBudget, evalConfigWithin_add, evalConfigWithin_add,
        enter_bad input output hFirst, PMF.pure_bind, hLoop,
        PMF.pure_bind]
      exact eval_halted _ 1 hHalt
    have hSupport : final ∈
        (evalConfigWithin program (entry input output)
          (5 * output.left.length + 10)).support := by
      rw [hFull]
      simp
    obtain ⟨used, hUsed, run⟩ :=
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
    exact ⟨final, used, hUsed, run, hHalt⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw 10 := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ :=
    runs_any (Tape.ofBits raw) ({} : Tape)
  have hInitial : Configuration.initial raw =
      entry (Tape.ofBits raw) ({} : Tape) := by
    cases raw <;> rfl
  rw [← hInitial] at run
  have hUsedTen : used ≤ 10 := by simpa using hUsed
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsedTen

theorem polynomialTime : PolynomialTime program :=
  ⟨fun _ => 10, PolynomiallyBounded.const 10, haltsWithin⟩

private def scanInput : Tape → Nat → Tape
  | input, 0 => input
  | input, count + 1 => scanInput input.moveRight.moveRight count

private def scanOutput : Tape → Nat → Tape
  | output, 0 => output
  | output, count + 1 => scanOutput output.moveLeft count

/-- With a complete stored modulus, the first-success branch scans exactly
one marked candidate cell pair per modulus bit. -/
theorem good_loop_matching (input output : Tape) (reversed : List Bool)
    (hLeft : output.left = reversed.map some) :
    evalConfigWithin program (goodLoop input output)
      (5 * reversed.length + 7) =
        PMF.pure (goodFinish (scanInput input reversed.length)
          (scanOutput output reversed.length)
          ((scanInput input reversed.length).current == some true)) := by
  induction reversed generalizing input output with
  | nil =>
      have hBlank : output.moveLeft.current = none := by
        simp [Tape.moveLeft, hLeft]
      simpa [scanInput, scanOutput] using good_stop input output hBlank
  | cons bit rest ih =>
      have hBit : output.moveLeft.current = some bit := by
        simp [Tape.moveLeft, hLeft]
      have hRest : output.moveLeft.left = rest.map some := by
        simp [Tape.moveLeft, hLeft]
      have hBudget : 5 * (bit :: rest).length + 7 =
          5 + (5 * rest.length + 7) := by simp; omega
      rw [hBudget, evalConfigWithin_add, good_cycle input output bit hBit,
        PMF.pure_bind]
      simpa [scanInput, scanOutput] using
        ih input.moveRight.moveRight output.moveLeft hRest

/-- The first-failure branch still scans the finite candidate and writes
false, irrespective of the second range decision. -/
theorem bad_loop_matching (input output : Tape) (reversed : List Bool)
    (hLeft : output.left = reversed.map some) :
    evalConfigWithin program (badLoop input output)
      (5 * reversed.length + 6) =
        PMF.pure (badFinish (scanInput input reversed.length)
          (scanOutput output reversed.length)) := by
  induction reversed generalizing input output with
  | nil =>
      have hBlank : output.moveLeft.current = none := by
        simp [Tape.moveLeft, hLeft]
      simpa [scanInput, scanOutput] using bad_stop input output hBlank
  | cons bit rest ih =>
      have hBit : output.moveLeft.current = some bit := by
        simp [Tape.moveLeft, hLeft]
      have hRest : output.moveLeft.left = rest.map some := by
        simp [Tape.moveLeft, hLeft]
      have hBudget : 5 * (bit :: rest).length + 6 =
          5 + (5 * rest.length + 6) := by simp; omega
      rw [hBudget, evalConfigWithin_add, bad_cycle input output bit hBit,
        PMF.pure_bind]
      simpa [scanInput, scanOutput] using
        ih input.moveRight.moveRight output.moveLeft hRest

private theorem scanInput_status (input : Tape) (bits : List Bool)
    (status : Bool) (tail : List (Option Bool))
    (hRight : input.right =
      (DelimitedTapeComparison.marked bits).map some ++ some status :: tail) :
    (scanInput input.moveRight bits.length).current = some status := by
  induction bits generalizing input with
  | nil =>
      simp [scanInput, DelimitedTapeComparison.marked, hRight, Tape.moveRight]
  | cons bit rest ih =>
      have hNext : (input.moveRight.moveRight).right =
          (DelimitedTapeComparison.marked rest).map some ++ some status :: tail := by
        simp [hRight, DelimitedTapeComparison.marked, Tape.moveRight]
      simpa [scanInput] using ih input.moveRight.moveRight hNext

private theorem scanInput_layout (input : Tape) (bits : List Bool)
    (status : Bool) (tail : List (Option Bool))
    (hRight : input.right =
      (DelimitedTapeComparison.marked bits).map some ++ some status :: tail) :
    scanInput input.moveRight bits.length =
      { left := (DelimitedTapeComparison.marked bits).reverse.map some ++
          input.current :: input.left,
        current := some status, right := tail } := by
  induction bits generalizing input with
  | nil =>
      simp [scanInput, DelimitedTapeComparison.marked, hRight, Tape.moveRight]
  | cons bit rest ih =>
      have hNext : (input.moveRight.moveRight).right =
          (DelimitedTapeComparison.marked rest).map some ++ some status :: tail := by
        simp [hRight, DelimitedTapeComparison.marked, Tape.moveRight]
      simpa [scanInput, Tape.moveRight, hRight, DelimitedTapeComparison.marked,
        List.reverse_cons, List.map_append, List.append_assoc] using
        ih input.moveRight.moveRight hNext

/-- For an equal-width comparison layout the status gate's second read is
the actual second candidate range decision, rather than an unrelated cell. -/
theorem scan_second_status (input : Tape) (second : List Bool)
    (status : Bool) (tail : List (Option Bool))
    (hRight : input.right =
      (DelimitedTapeComparison.marked second).map some ++ some status :: tail) :
    (scanInput input.moveRight second.length).current = some status :=
  scanInput_status input second status tail hRight

private theorem scanOutput_blank_layout (reversed : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    (scanOutput ({ left := reversed.map some, current := current, right := right } : Tape)
      reversed.length).moveLeft =
      ({ right := reversed.reverse.map some ++ current :: right } : Tape) := by
  induction reversed generalizing current right with
  | nil => rfl
  | cons bit rest ih =>
      simpa [scanOutput, Tape.moveLeft, List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit) (current :: right)

/-- The gate writes the conjunction of the two range decisions at the
reserved cell preceding the retained modulus. -/
theorem eval_matching_layout (input output : Tape)
    (second reversed : List Bool) (firstStatus secondStatus : Bool)
    (tail : List (Option Bool))
    (hFirst : input.current = some firstStatus)
    (hRight : input.right =
      (DelimitedTapeComparison.marked second).map some ++ some secondStatus :: tail)
    (hLeft : output.left = reversed.map some)
    (hWidth : second.length = reversed.length) :
    ∃ finish,
      evalConfigWithin program (entry input output)
        (5 * reversed.length + 10) = PMF.pure finish ∧
      finish.halted = true ∧
      finish.inputTape.current = some false ∧
      finish.outputTape.left.getD 0 none = some (firstStatus && secondStatus) ∧
      finish.inputTape =
        { left := (DelimitedTapeComparison.marked second).reverse.map some ++
            some false :: input.left,
          current := some false, right := tail } ∧
      finish.outputTape =
        ({ current := some (firstStatus && secondStatus),
           right := reversed.reverse.map some ++ output.current :: output.right } : Tape).moveRight := by
  have hOutputLayout : (scanOutput output reversed.length).moveLeft =
      ({ right := reversed.reverse.map some ++ output.current :: output.right } : Tape) := by
    have h := scanOutput_blank_layout reversed output.current output.right
    have hOut : output = ({ left := reversed.map some, current := output.current, right := output.right } : Tape) := by
      cases output
      simp_all
    simpa only [← hOut] using h
  have hSecond : (scanInput (input.write (some false)).moveRight reversed.length).current =
      some secondStatus := by
    rw [← hWidth]
    exact scan_second_status (input.write (some false)) second secondStatus tail hRight
  have hRestored : scanInput (input.write (some false)).moveRight reversed.length =
      { left := (DelimitedTapeComparison.marked second).reverse.map some ++
          some false :: input.left,
        current := some secondStatus, right := tail } := by
    rw [← hWidth]
    exact scanInput_layout (input.write (some false)) second secondStatus tail hRight
  cases firstStatus with
  | true =>
      let finish := goodFinish
        (scanInput (input.write (some false)).moveRight reversed.length)
        (scanOutput output reversed.length) secondStatus
      refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · have hBudget : 5 * reversed.length + 10 =
            3 + (5 * reversed.length + 7) := by omega
        rw [hBudget, evalConfigWithin_add,
          enter_good input output (by simpa using hFirst), PMF.pure_bind]
        simpa [finish, hSecond] using
          good_loop_matching (input.write (some false)).moveRight output reversed hLeft
      · simp [finish, goodFinish, badFinish, Tape.write]
      · cases hTail : (scanOutput output reversed.length).moveLeft.right <;>
          simp [finish, goodFinish, Tape.moveRight, Tape.write, hTail]
      · change (scanInput (input.write (some false)).moveRight reversed.length).write
          (some false) = _
        rw [hRestored]
        rfl
      · simp only [finish, goodFinish]
        rw [hOutputLayout]
        rfl
  | false =>
      let finish := badFinish
        (scanInput (input.write (some false)).moveRight reversed.length)
        (scanOutput output reversed.length)
      refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · have hBudget : 5 * reversed.length + 10 =
            (3 + (5 * reversed.length + 6)) + 1 := by omega
        rw [hBudget, evalConfigWithin_add, evalConfigWithin_add,
          enter_bad input output (by intro h; rw [hFirst] at h; cases h), PMF.pure_bind,
          bad_loop_matching (input.write (some false)).moveRight output reversed hLeft,
          PMF.pure_bind]
        exact eval_halted _ 1 rfl
      · simp [finish, goodFinish, badFinish, Tape.write]
      · cases hTail : (scanOutput output reversed.length).moveLeft.right <;>
          simp [finish, badFinish, Tape.moveRight, Tape.write, hTail]
      · change (scanInput (input.write (some false)).moveRight reversed.length).write
          (some false) = _
        rw [hRestored]
        rfl
      · simp only [finish, badFinish]
        rw [hOutputLayout]
        rfl

/-- Status and restored-input projection of the complete layout theorem. -/
theorem eval_matching_decisions (input output : Tape)
    (second reversed : List Bool) (firstStatus secondStatus : Bool)
    (tail : List (Option Bool))
    (hFirst : input.current = some firstStatus)
    (hRight : input.right =
      (DelimitedTapeComparison.marked second).map some ++ some secondStatus :: tail)
    (hLeft : output.left = reversed.map some)
    (hWidth : second.length = reversed.length) :
    ∃ finish,
      evalConfigWithin program (entry input output)
        (5 * reversed.length + 10) = PMF.pure finish ∧
      finish.halted = true ∧ finish.inputTape.current = some false ∧
      finish.outputTape.left.getD 0 none = some (firstStatus && secondStatus) ∧
      finish.inputTape =
        { left := (DelimitedTapeComparison.marked second).reverse.map some ++
            some false :: input.left, current := some false, right := tail } := by
  obtain ⟨finish, hEval, hHalt, hCurrent, hStatus, hInput, _⟩ :=
    eval_matching_layout input output second reversed firstStatus secondStatus tail
      hFirst hRight hLeft hWidth
  exact ⟨finish, hEval, hHalt, hCurrent, hStatus, hInput⟩

/-- The gate can be invoked directly on the halted physical layout of the
first comparator, retaining its first decision at the current input cell
and finding the second decision after the marked second field. -/
theorem runs_from_compared_layout (prior : Ordering)
    (beforeInput : List (Option Bool)) (modulus second tail suffix : List Bool)
    (secondStatus : Bool) (hWidth : second.length = modulus.length) :
    let compared := DelimitedTapeComparison.done prior beforeInput
      (modulus.reverse.map some)
      (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
    ∃ finish used,
      RunsFor program (entry compared.inputTape compared.outputTape) finish used ∧
      finish.halted = true ∧
      finish.inputTape.current = some false ∧
      finish.outputTape.left.getD 0 none =
        some ((prior == Ordering.lt) && secondStatus) ∧
      finish.inputTape =
        { Tape.ofBits (false :: tail) with
          left := (DelimitedTapeComparison.marked second).reverse.map some ++
            some false :: beforeInput } ∧
      finish.outputTape =
        ({ current := some ((prior == Ordering.lt) && secondStatus),
           right := modulus.map some ++ (Tape.ofBits suffix).current :: (Tape.ofBits suffix).right } : Tape).moveRight := by
  dsimp only
  let compared := DelimitedTapeComparison.done prior beforeInput
    (modulus.reverse.map some)
    (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
  have hFirst : compared.inputTape.current = some (prior == Ordering.lt) := by
    simp [compared, DelimitedTapeComparison.done, Tape.write]
  have hRight : compared.inputTape.right =
      (DelimitedTapeComparison.marked second).map some ++
        some secondStatus :: tail.map some := by
    simp [compared, DelimitedTapeComparison.done, Tape.write,
      Tape.ofBits, List.map_append]
  have hLeft : compared.outputTape.left = modulus.reverse.map some := by
    rfl
  obtain ⟨finish, hEval, hHalt, hSecond, hCombined, hRestored, hOutput⟩ :=
    eval_matching_layout compared.inputTape compared.outputTape
      second modulus.reverse (prior == Ordering.lt) secondStatus
      (tail.map some) hFirst hRight hLeft (by simp [hWidth])
  have hSupport : finish ∈
      (evalConfigWithin program
        (entry compared.inputTape compared.outputTape)
        (5 * modulus.reverse.length + 10)).support := by
    rw [hEval]
    simp
  obtain ⟨used, _, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  refine ⟨finish, used, run, hHalt, hSecond, hCombined, ?_, ?_⟩
  · simpa [compared, DelimitedTapeComparison.done, Tape.ofBits, Tape.write] using hRestored
  · simpa [compared, DelimitedTapeComparison.done, Tape.write] using hOutput

/-- Backwards-compatible input/status projection. The full output layout is
available from `runs_from_compared_layout` for native workspace cleanup. -/
theorem runs_from_compared (prior : Ordering)
    (beforeInput : List (Option Bool)) (modulus second tail suffix : List Bool)
    (secondStatus : Bool) (hWidth : second.length = modulus.length) :
    let compared := DelimitedTapeComparison.done prior beforeInput
      (modulus.reverse.map some)
      (DelimitedTapeComparison.marked second ++ secondStatus :: tail) suffix
    ∃ finish used,
      RunsFor program (entry compared.inputTape compared.outputTape) finish used ∧
      finish.halted = true ∧ finish.inputTape.current = some false ∧
      finish.outputTape.left.getD 0 none = some ((prior == Ordering.lt) && secondStatus) ∧
      finish.inputTape =
        { Tape.ofBits (false :: tail) with
          left := (DelimitedTapeComparison.marked second).reverse.map some ++
            some false :: beforeInput } := by
  obtain ⟨finish, used, run, hHalt, hCurrent, hStatus, hInput, _⟩ :=
    runs_from_compared_layout prior beforeInput modulus second tail suffix secondStatus hWidth
  exact ⟨finish, used, run, hHalt, hCurrent, hStatus, hInput⟩

end Machine.ChooseRangeStatusGate
