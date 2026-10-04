import Foundation.Machine.ChooseSecondRangeCheck

namespace Machine.ChooseFirstFieldRewind

/-- From the second range decision, rewind four marked response cells per
stored modulus bit. The input head then points at the first candidate and
the output head points at the first modulus bit. The decision cell remains
on the input tape. -/
def program : Program :=
  [.moveLeft .input,
   .moveLeft .output,
   .branch .output 8 3 3,
   .moveLeft .input,
   .moveLeft .input,
   .moveLeft .input,
   .moveLeft .input,
   .jump 1,
   .moveRight .output,
   .halt]

def entry (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

def loop (input output : Tape) : Configuration :=
  { pc := 1, inputTape := input, outputTape := output }

def finish (input output : Tape) : Configuration :=
  { pc := 9, inputTape := input,
    outputTape := output.moveLeft.moveRight, halted := true }

private def moveLeftFour (t : Tape) : Tape :=
  t.moveLeft.moveLeft.moveLeft.moveLeft

theorem enter (input output : Tape) :
    evalConfigWithin program (entry input output) 1 =
      PMF.pure (loop input.moveLeft output) := by
  simp [evalConfigWithin, stepPMF, next, program, entry, loop,
    Instruction.next, Configuration.advance, Configuration.updateTape]

theorem cycle (input output : Tape) (bit : Bool)
    (hBit : output.moveLeft.current = some bit) :
    evalConfigWithin program (loop input output) 7 =
      PMF.pure (loop (moveLeftFour input) output.moveLeft) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, loop,
      moveLeftFour, hBit, Instruction.next, Configuration.advance,
      Configuration.updateTape, Configuration.tape, PMF.pure_bind]

theorem stop (input output : Tape)
    (hBlank : output.moveLeft.current = none) :
    evalConfigWithin program (loop input output) 4 =
      PMF.pure (finish input output) := by
  simp [evalConfigWithin, stepPMF, next, program, loop, finish,
    hBlank, Instruction.next, Configuration.advance,
    Configuration.updateTape, Configuration.tape, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, stepPMF, next, h, ih]

/-- Any finite output prefix eventually reaches a blank. This is an
operational bound, including malformed and prematurely blank tapes. -/
theorem loop_any (input output : Tape) :
    ∃ final, final.halted = true ∧
      evalConfigWithin program (loop input output)
        (7 * output.left.length + 4) = PMF.pure final := by
  cases hLeft : output.left with
  | nil =>
      refine ⟨finish input output, rfl, ?_⟩
      simpa [hLeft, Tape.moveLeft] using
        stop input output (by simp [Tape.moveLeft, hLeft])
  | cons cell rest =>
      cases cell with
      | none =>
          refine ⟨finish input output, rfl, ?_⟩
          have hBlank : output.moveLeft.current = none := by
            simp [Tape.moveLeft, hLeft]
          have hStop := stop input output hBlank
          have hBudget : 7 * output.left.length + 4 =
              4 + 7 * output.left.length := by omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hStop, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | some bit =>
          let nextInput := moveLeftFour input
          let nextOutput := output.moveLeft
          obtain ⟨final, hHalt, hEval⟩ := loop_any nextInput nextOutput
          refine ⟨final, hHalt, ?_⟩
          have hCycle := cycle input output bit (by simp [Tape.moveLeft, hLeft])
          have hLength : nextOutput.left.length = rest.length := by
            simp [nextOutput, Tape.moveLeft, hLeft]
          have hBudget : 7 * output.left.length + 4 =
              7 + (7 * nextOutput.left.length + 4) := by
            simp only [hLeft, List.length_cons, hLength]
            omega
          simp only [hLeft] at hBudget
          rw [hBudget, evalConfigWithin_add, hCycle, PMF.pure_bind]
          exact hEval
termination_by output.left.length
decreasing_by simp [nextOutput, Tape.moveLeft, hLeft]

theorem runs_any (input output : Tape) :
    ∃ final used, used ≤ 7 * output.left.length + 5 ∧
      RunsFor program (entry input output) final used ∧
      final.halted = true := by
  obtain ⟨final, hHalt, hEval⟩ := loop_any input.moveLeft output
  have hFull : evalConfigWithin program (entry input output)
      (7 * output.left.length + 5) = PMF.pure final := by
    have hBudget : 7 * output.left.length + 5 =
        1 + (7 * output.left.length + 4) := by omega
    rw [hBudget, evalConfigWithin_add, enter, PMF.pure_bind]
    exact hEval
  have hSupport : final ∈
      (evalConfigWithin program (entry input output)
        (7 * output.left.length + 5)).support := by
    rw [hFull]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨final, used, hUsed, run, hHalt⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (7 * (raw.length + 1) + 5) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ :=
    runs_any (Tape.ofBits raw) ({} : Tape)
  have hInitial : Configuration.initial raw =
      entry (Tape.ofBits raw) ({} : Tape) := by
    cases raw <;> rfl
  rw [← hInitial] at run
  have hUsedFive : used ≤ 5 := by simpa using hUsed
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (by omega)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 7 * (length + 1) + 5,
    ((PolynomiallyBounded.const 7).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
        (PolynomiallyBounded.const 5), haltsWithin⟩

private def rewindInput (input : Tape) : Nat → Tape
  | 0 => input
  | width + 1 => rewindInput (moveLeftFour input) width

private def rewindOutput (output : Tape) : Nat → Tape
  | 0 => output
  | width + 1 => rewindOutput output.moveLeft width

private def moveLeftN (tape : Tape) : Nat → Tape
  | 0 => tape
  | count + 1 => moveLeftN tape.moveLeft count

private theorem moveLeftN_four (tape : Tape) (count : Nat) :
    moveLeftN tape (count + 4) = moveLeftN (moveLeftFour tape) count := by
  rw [show count + 4 = ((((count + 1) + 1) + 1) + 1) by omega]
  rfl

private theorem rewindInput_eq (tape : Tape) (width : Nat) :
    rewindInput tape width = moveLeftN tape (4 * width) := by
  induction width generalizing tape with
  | zero => rfl
  | succ width ih =>
      rw [rewindInput, ih, Nat.mul_succ, moveLeftN_four]

private theorem rewindOutput_eq (tape : Tape) (width : Nat) :
    rewindOutput tape width = moveLeftN tape width := by
  induction width generalizing tape with
  | zero => rfl
  | succ width ih => simpa [rewindOutput, moveLeftN] using ih tape.moveLeft

private theorem moveLeftN_prefix (prefixCells : List (Option Bool))
    (marker : Option Bool) (before right : List (Option Bool))
    (current : Option Bool) :
    moveLeftN
      { left := prefixCells ++ marker :: before, current := current, right := right }
      (prefixCells.length + 1) =
      { left := before, current := marker,
        right := prefixCells.reverse ++ current :: right } := by
  induction prefixCells generalizing current right with
  | nil => simp [moveLeftN, Tape.moveLeft]
  | cons cell rest ih =>
      simpa [moveLeftN, Tape.moveLeft, List.reverse_cons,
        List.append_assoc] using ih (current :: right) cell

private theorem getD_append_none (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ] using ih i

private theorem marked_length (bits : List Bool) :
    (DelimitedTapeComparison.marked bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [DelimitedTapeComparison.marked, ih]; omega

private theorem rewind_prefix_eq (bit : Bool) (rest tail : List Bool)
    (status : Bool) (before : List (Option Bool)) :
    moveLeftN
      { Tape.ofBits (status :: tail) with
        left := (bit :: rest).reverse.map some ++ before }
      (bit :: rest).length =
      { Tape.ofBits ((bit :: rest) ++ status :: tail) with left := before } := by
  have h := moveLeftN_prefix (rest.reverse.map some)
    (some bit) before (Tape.ofBits (status :: tail)).right
      (Tape.ofBits (status :: tail)).current
  simpa [Tape.ofBits, List.reverse_cons, List.map_append,
    List.append_assoc] using h

private theorem rewind_modulus_equivalent (modulus suffix : List Bool) :
    (rewindOutput
      { Tape.ofBits suffix with left := modulus.reverse.map some }
      modulus.length).Equivalent (Tape.ofBits (modulus ++ suffix)) := by
  rw [rewindOutput_eq]
  cases modulus with
  | nil => cases suffix <;> simp [moveLeftN, Tape.Equivalent, Tape.ofBits]
  | cons bit rest =>
      have h := moveLeftN_prefix (rest.reverse.map some) (some bit) []
        (Tape.ofBits suffix).right (Tape.ofBits suffix).current
      have hTape : moveLeftN
          { Tape.ofBits suffix with
            left := (bit :: rest).reverse.map some }
          (bit :: rest).length =
          { left := [], current := some bit,
            right := rest.map some ++ (Tape.ofBits suffix).current ::
              (Tape.ofBits suffix).right } := by
        simpa [Tape.ofBits, List.reverse_cons, List.map_append,
          List.append_assoc] using h
      rw [hTape]
      cases suffix with
      | nil =>
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro i
          simpa [Tape.ofBits] using getD_append_none (rest.map some) i
      | cons suffixBit suffixRest =>
          simp [Tape.Equivalent, Tape.ofBits, List.map_append]

private theorem rewind_nonempty_prefix_eq (fieldPrefix tail : List Bool)
    (status : Bool) (before : List (Option Bool))
    (hNonempty : fieldPrefix ≠ []) :
    moveLeftN
      { Tape.ofBits (status :: tail) with
        left := fieldPrefix.reverse.map some ++ before } fieldPrefix.length =
      { Tape.ofBits (fieldPrefix ++ status :: tail) with left := before } := by
  cases fieldPrefix with
  | nil => exact (hNonempty rfl).elim
  | cons bit rest => exact rewind_prefix_eq bit rest tail status before

/-- With a contiguous stored modulus prefix, the loop takes exactly one
cycle per modulus bit, independently of those bits' values. -/
theorem eval_matching_left (input output : Tape) (reversed : List Bool)
    (hLeft : output.left = reversed.map some) :
    evalConfigWithin program (loop input output) (7 * reversed.length + 4) =
      PMF.pure (finish (rewindInput input reversed.length)
        (rewindOutput output reversed.length)) := by
  induction reversed generalizing input output with
  | nil =>
      have hBlank : output.moveLeft.current = none := by
        simp [Tape.moveLeft, hLeft]
      simpa [rewindInput, rewindOutput] using stop input output hBlank
  | cons bit rest ih =>
      have hBit : output.moveLeft.current = some bit := by
        simp [Tape.moveLeft, hLeft]
      have hRest : output.moveLeft.left = rest.map some := by
        simp [Tape.moveLeft, hLeft]
      have hBudget : 7 * (bit :: rest).length + 4 =
          7 + (7 * rest.length + 4) := by simp; omega
      rw [hBudget, evalConfigWithin_add, cycle input output bit hBit,
        PMF.pure_bind]
      simpa [rewindInput, rewindOutput, moveLeftFour] using
        ih (moveLeftFour input) output.moveLeft hRest

theorem runs_matching_left (input output : Tape) (reversed : List Bool)
    (hLeft : output.left = reversed.map some) :
    ∃ used, used ≤ 1 + (7 * reversed.length + 4) ∧
      RunsFor program (entry input output)
        (finish (rewindInput input.moveLeft reversed.length)
          (rewindOutput output reversed.length)) used := by
  have hEval : evalConfigWithin program (entry input output)
      (1 + (7 * reversed.length + 4)) =
      PMF.pure (finish (rewindInput input.moveLeft reversed.length)
        (rewindOutput output reversed.length)) := by
    rw [evalConfigWithin_add, enter, PMF.pure_bind]
    exact eval_matching_left input.moveLeft output reversed hLeft
  have hSupport : (finish (rewindInput input.moveLeft reversed.length)
      (rewindOutput output reversed.length)) ∈
      (evalConfigWithin program (entry input output)
        (1 + (7 * reversed.length + 4))).support := by
    rw [hEval]
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le

/-- On two equal-width marked response fields, the rewind restores the
first candidate and the original modulus to their initial heads. It
preserves the second comparison decision in the unconsumed input suffix. -/
theorem runs_matching_layout (width : Nat)
    (before : List (Option Bool))
    (first second modulus suffix tail : List Bool) (status : Bool)
    (hFirst : first.length = width) (hSecond : second.length = width)
    (hModulus : modulus.length = width) :
    let input : Tape :=
      { Tape.ofBits (status :: tail) with
        left := (DelimitedTapeComparison.marked second).reverse.map some ++
          (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: before }
    let output : Tape :=
      { Tape.ofBits suffix with left := modulus.reverse.map some }
    ∃ target used,
      RunsFor program (entry input output) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit first ++
            DelimitedTapeComparison.marked second ++ status :: tail) with
          left := some false :: before } ∧
      target.outputTape.Equivalent (Tape.ofBits (modulus ++ suffix)) := by
  dsimp only
  let input : Tape :=
    { Tape.ofBits (status :: tail) with
      left := (DelimitedTapeComparison.marked second).reverse.map some ++
        (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: before }
  let output : Tape :=
    { Tape.ofBits suffix with left := modulus.reverse.map some }
  obtain ⟨used, _, run⟩ := runs_matching_left input output modulus.reverse (by rfl)
  let target := finish (rewindInput input.moveLeft modulus.reverse.length)
    (rewindOutput output modulus.reverse.length)
  refine ⟨target, used, run, rfl, ?_, ?_⟩
  · let fieldPrefix := FiniteBitEncoding.delimit first ++
      DelimitedTapeComparison.marked second
    have hPrefixLength : fieldPrefix.length = 4 * width + 1 := by
      simp [fieldPrefix, marked_length, hFirst, hSecond]
      omega
    have hNonempty : fieldPrefix ≠ [] := by
      intro h
      have hZero : fieldPrefix.length = 0 := by simp [h]
      omega
    have hInput : input =
        { Tape.ofBits (status :: tail) with
          left := fieldPrefix.reverse.map some ++ some false :: before } := by
      simp [input, fieldPrefix, List.reverse_append, List.map_append,
        List.append_assoc]
    have hRewound : rewindInput input.moveLeft modulus.reverse.length =
        { Tape.ofBits (fieldPrefix ++ status :: tail) with
          left := some false :: before } := by
      rw [rewindInput_eq]
      have hWidth : modulus.reverse.length = width := by
        simpa using hModulus
      rw [hWidth]
      have hCount : 4 * width + 1 = fieldPrefix.length := hPrefixLength.symm
      change moveLeftN input (4 * width + 1) = _
      rw [hCount, hInput]
      exact rewind_nonempty_prefix_eq fieldPrefix tail status
        (some false :: before) hNonempty
    change (rewindInput input.moveLeft modulus.reverse.length).Equivalent _
    rw [hRewound]
    exact Tape.Equivalent.refl _
  · have hOutput : (rewindOutput output modulus.reverse.length).Equivalent
        (Tape.ofBits (modulus ++ suffix)) := by
      simpa [output, hModulus] using
        rewind_modulus_equivalent modulus suffix
    exact (Tape.moveLeft_moveRight_equivalent
      (rewindOutput output modulus.reverse.length)).trans hOutput

/-- The exact stopped state of the preceding range comparator is an
ordinary starting state for this finite rewind, without reloading tapes. -/
theorem runs_from_compared (width : Nat)
    (before : List (Option Bool))
    (first second modulus suffix tail : List Bool)
    (hFirst : first.length = width) (hSecond : second.length = width)
    (hModulus : modulus.length = width) :
    let beforeSecond :=
      (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: before
    let compared := DelimitedTapeComparison.done
      (BinaryComparison.compare Ordering.eq (second.zip modulus))
      ((DelimitedTapeComparison.marked second).reverse.map some ++ beforeSecond)
      (modulus.reverse.map some) tail suffix
    ∃ target used,
      RunsFor program (entry compared.inputTape compared.outputTape) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit first ++
            DelimitedTapeComparison.marked second ++
              (BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt)
                :: tail) with
          left := some false :: before } ∧
      target.outputTape.Equivalent (Tape.ofBits (modulus ++ suffix)) := by
  dsimp only
  let status :=
    BinaryComparison.compare Ordering.eq (second.zip modulus) == Ordering.lt
  simpa [DelimitedTapeComparison.done, Tape.write, Tape.ofBits, status,
    List.map_reverse, List.append_assoc] using
    runs_matching_layout width before first second modulus suffix tail
      status hFirst hSecond hModulus

end Machine.ChooseFirstFieldRewind
