import Foundation.Crypto.Semantics.Machine.BinaryColumnSlotFill
import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison

namespace Machine.DelimitedColumnSlotFill

/-- Copy marker/payload pairs into one slot of successive three-cell
arithmetic columns. The false delimiter remains under the input head.
Neither the other two column slots nor the retained input prefix is erased. -/
def program : Program :=
  [.branch .input 12 12 1,
   .moveRight .input,
   .branch .input 12 3 5,
   .write .output false, .jump 7,
   .write .output true, .jump 7,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .moveRight .input, .jump 0,
   .halt]

def entry (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

def finish (input output : Tape) : Configuration :=
  { pc := 12, inputTape := input, outputTape := output, halted := true }

private def shiftOutput (output : Tape) (bit : Bool) : Tape :=
  (output.write (some bit)).moveRight.moveRight.moveRight

theorem pair (input output : Tape) (bit : Bool)
    (hMarker : input.current = some true)
    (hBit : input.moveRight.current = some bit) :
    evalConfigWithin program (entry input output) 10 =
      PMF.pure (entry input.moveRight.moveRight (shiftOutput output bit)) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, entry,
      shiftOutput, hMarker, hBit, Instruction.next, Configuration.advance,
      Configuration.tape, Configuration.updateTape, PMF.pure_bind]

theorem stop (input output : Tape) (hMarker : input.current ≠ some true) :
    evalConfigWithin program (entry input output) 2 =
      PMF.pure (finish input output) := by
  cases hCurrent : input.current with
  | none =>
      simp [evalConfigWithin, stepPMF, next, program, entry, finish,
        hCurrent, Instruction.next, Configuration.tape, PMF.pure_bind]
  | some bit =>
      cases bit
      · simp [evalConfigWithin, stepPMF, next, program, entry, finish,
          hCurrent, Instruction.next, Configuration.tape, PMF.pure_bind]
      · exact (hMarker hCurrent).elim

theorem missing_payload (input output : Tape)
    (hMarker : input.current = some true)
    (hBlank : input.moveRight.current = none) :
    evalConfigWithin program (entry input output) 4 =
      PMF.pure (finish input.moveRight output) := by
  simp [evalConfigWithin, stepPMF, next, program, entry, finish,
    hMarker, hBlank, Instruction.next, Configuration.advance,
    Configuration.tape, Configuration.updateTape, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, stepPMF, next, h, ih]

/-- Every iteration consumes a complete pair, so truncated and malformed
finite tapes halt as well. No arithmetic validity premise is used. -/
theorem eval_any (input output : Tape) :
    ∃ final,
      evalConfigWithin program (entry input output)
        (10 * (input.right.length + 1) + 4) = PMF.pure final ∧
      final.halted = true := by
  by_cases hMarker : input.current = some true
  · cases hPayload : input.moveRight.current with
    | none =>
        refine ⟨finish input.moveRight output, ?_, rfl⟩
        have h := missing_payload input output hMarker hPayload
        have hBudget : 10 * (input.right.length + 1) + 4 =
            4 + 10 * (input.right.length + 1) := by omega
        rw [hBudget, evalConfigWithin_add, h, PMF.pure_bind]
        exact eval_halted _ _ rfl
    | some bit =>
        let nextInput := input.moveRight.moveRight
        let nextOutput := shiftOutput output bit
        obtain ⟨final, hEval, hHalt⟩ := eval_any nextInput nextOutput
        have hDecrease : nextInput.right.length < input.right.length := by
          cases hRight : input.right with
          | nil => simp [Tape.moveRight, hRight] at hPayload
          | cons cell rest =>
              cases rest <;> simp [nextInput, Tape.moveRight, hRight] <;> omega
        have hUsed : 10 + (10 * (nextInput.right.length + 1) + 4) ≤
            10 * (input.right.length + 1) + 4 := by omega
        have hBudget : 10 * (input.right.length + 1) + 4 =
            (10 + (10 * (nextInput.right.length + 1) + 4)) +
              (10 * (input.right.length + 1) + 4 -
                (10 + (10 * (nextInput.right.length + 1) + 4))) := by omega
        refine ⟨final, ?_, hHalt⟩
        rw [hBudget, evalConfigWithin_add, evalConfigWithin_add,
          pair input output bit hMarker hPayload, PMF.pure_bind, hEval,
          PMF.pure_bind]
        exact eval_halted _ _ hHalt
  · refine ⟨finish input output, ?_, rfl⟩
    have h := stop input output hMarker
    have hBudget : 10 * (input.right.length + 1) + 4 =
        2 + (10 * (input.right.length + 1) + 2) := by omega
    rw [hBudget, evalConfigWithin_add, h, PMF.pure_bind]
    exact eval_halted _ _ rfl
termination_by input.right.length
decreasing_by
  cases hRight : input.right with
  | nil => simp [Tape.moveRight, hRight] at hPayload
  | cons cell rest =>
      cases rest <;> simp [nextInput, Tape.moveRight, hRight] <;> omega

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

theorem runs_any (input output : Tape) :
    ∃ final used,
      used ≤ 10 * (input.right.length + 1) + 4 ∧
      RunsFor program (entry input output) final used ∧ final.halted = true := by
  obtain ⟨final, hEval, hHalt⟩ := eval_any input output
  have hSupport : final ∈
      (evalConfigWithin program (entry input output)
        (10 * (input.right.length + 1) + 4)).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨final, used, hUsed, run, hHalt⟩

theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (10 * (raw.length + 1) + 4) := by
  obtain ⟨final, used, hUsed, run, hHalt⟩ :=
    runs_any (Tape.ofBits raw) ({} : Tape)
  have hInitial : Configuration.initial raw =
      entry (Tape.ofBits raw) ({} : Tape) := by cases raw <;> rfl
  rw [← hInitial] at run
  have hRight : (Tape.ofBits raw).right.length ≤ raw.length := by
    cases raw <;> simp [Tape.ofBits]
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit (by omega)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 10 * (length + 1) + 4,
    ((PolynomiallyBounded.const 10).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
        (PolynomiallyBounded.const 4), haltsWithin⟩

/-- The operational copier realizes the existing column-writing algebra
without reloading any tape. Trailing raw state remains unread. -/
theorem eval_field (before : List (Option Bool)) (field tail : List Bool)
    (output : Tape) :
    evalConfigWithin program
      (entry { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with left := before }
        output) (10 * field.length + 2) =
      PMF.pure (finish
        { Tape.ofBits (false :: tail) with
          left := (DelimitedTapeComparison.marked field).reverse.map some ++ before }
        (BinaryColumnSlotFill.fillTape output field)) := by
  induction field generalizing before output with
  | nil =>
      simp only [FiniteBitEncoding.delimit, List.nil_append,
        DelimitedTapeComparison.marked, List.reverse_nil, List.map_nil,
        List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add,
        BinaryColumnSlotFill.fillTape]
      exact stop _ _ (by simp [Tape.ofBits])
  | cons bit rest ih =>
      let input : Tape :=
        { Tape.ofBits (FiniteBitEncoding.delimit (bit :: rest) ++ tail) with left := before }
      have hMarker : input.current = some true := rfl
      have hBit : input.moveRight.current = some bit := rfl
      have hNext : input.moveRight.moveRight =
          { Tape.ofBits (FiniteBitEncoding.delimit rest ++ tail) with
            left := some bit :: some true :: before } := by
        cases rest <;>
          simp [input, FiniteBitEncoding.delimit, Tape.ofBits, Tape.moveRight]
      have hBudget : 10 * (bit :: rest).length + 2 =
          10 + (10 * rest.length + 2) := by simp; omega
      change evalConfigWithin program (entry input output) _ = _
      rw [hBudget, evalConfigWithin_add, pair input output bit hMarker hBit,
        PMF.pure_bind, hNext]
      simpa [BinaryColumnSlotFill.fillTape, shiftOutput,
        DelimitedTapeComparison.marked, List.reverse_cons, List.map_append,
        List.append_assoc] using
        ih (some bit :: some true :: before) (shiftOutput output bit)

/-- A width-matching candidate fills the first slot of the retained
modulus template with its actual bits. -/
theorem eval_first_slots (before : List (Option Bool))
    (field modulus tail : List Bool) (hWidth : field.length = modulus.length) :
    evalConfigWithin program
      (entry { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with left := before }
        (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)))
      (10 * field.length + 2) =
        PMF.pure (finish
          { Tape.ofBits (false :: tail) with
            left := (DelimitedTapeComparison.marked field).reverse.map some ++ before }
          { left := (BinaryColumnSlotFill.firstSlots field modulus).reverse.map some }) := by
  rw [eval_field]
  have hFill := BinaryColumnSlotFill.fillTape_first field modulus hWidth []
  have hEmpty : ({ Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
      left := [] } : Tape) = Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) := by
    cases BinaryThirdColumnTemplate.columns modulus <;> rfl
  rw [hEmpty] at hFill
  simpa using congrArg (fun tape => PMF.pure (finish
    { Tape.ofBits (false :: tail) with
      left := (DelimitedTapeComparison.marked field).reverse.map some ++ before }
    tape)) hFill

/-- Copy a delimited candidate into the first track of the power input while
retaining the exponent and modulus previously copied from the instance. -/
theorem eval_power_slots (beforeInput beforeOutput : List (Option Bool))
    (old field exponent modulus tail : List Bool)
    (hOld : old.length = modulus.length)
    (hWidth : field.length = modulus.length)
    (hExponent : exponent.length = modulus.length) :
    evalConfigWithin program
      (entry { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
          left := beforeInput }
        { Tape.ofBits (BinaryColumnSlotFill.fullSlots old exponent modulus) with
          left := beforeOutput })
      (10 * field.length + 2) =
        PMF.pure (finish
          { Tape.ofBits (false :: tail) with
            left := (DelimitedTapeComparison.marked field).reverse.map some ++ beforeInput }
          { left := (BinaryColumnSlotFill.fullSlots field exponent modulus).reverse.map some ++
              beforeOutput }) := by
  rw [eval_field, BinaryColumnSlotFill.fillTape_first_full old field exponent modulus
    hOld hWidth hExponent beforeOutput]

end Machine.DelimitedColumnSlotFill
