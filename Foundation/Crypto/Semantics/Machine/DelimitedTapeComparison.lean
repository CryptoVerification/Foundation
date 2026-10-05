import Foundation.Crypto.Semantics.Machine.BinaryComparison
import Foundation.Crypto.Semantics.Machine.Encoding

namespace Machine.DelimitedTapeComparison

private def address : Ordering → Nat
  | .eq => 0
  | .lt => 17
  | .gt => 34

private def finishAddress : Ordering → Nat
  | .eq => 51
  | .lt => 53
  | .gt => 55

/-- One finite-control block compares one self-delimited candidate bit with
the current bit on the other tape. The more significant unequal pair
overrides the previous comparison, as required by little-endian codes. -/
private def block (prior : Ordering) : Program :=
  let base := address prior
  [.branch .input 57 (finishAddress prior) (base + 1),
   .moveRight .input,
   .branch .input 57 (base + 3) (base + 10),
   .branch .output 57 (base + 4) (base + 7),
   .moveRight .output,
   .moveRight .input,
   .jump (address prior),
   .moveRight .output,
   .moveRight .input,
   .jump (address .lt),
   .branch .output 57 (base + 11) (base + 14),
   .moveRight .output,
   .moveRight .input,
   .jump (address .gt),
   .moveRight .output,
   .moveRight .input,
   .jump (address prior)]

/-- The candidate is on the input tape as marker/payload pairs. The
equal-width modulus is read directly from the output tape. The final
status replaces the candidate delimiter on the input tape, leaving the
stored modulus and following instance fields untouched. -/
def program : Program :=
  block .eq ++ block .lt ++ block .gt ++
    [.write .input false, .halt,
     .write .input true, .halt,
     .write .input false, .halt,
     .write .input false, .halt]

def state (prior : Ordering) (beforeInput beforeOutput : List (Option Bool))
    (input output : List Bool) : Configuration :=
  { pc := address prior,
    inputTape := { Tape.ofBits input with left := beforeInput },
    outputTape := { Tape.ofBits output with left := beforeOutput } }

/-- Entry configuration with arbitrary retained tape contents. -/
def atState (prior : Ordering) (input output : Tape) : Configuration :=
  { pc := address prior, inputTape := input, outputTape := output }

@[simp] theorem atState_eq (input output : Tape) :
    atState Ordering.eq input output =
      { inputTape := input, outputTape := output } := rfl

def done (prior : Ordering) (beforeInput : List (Option Bool))
    (beforeOutput : List (Option Bool)) (tail output : List Bool) : Configuration :=
  { pc := finishAddress prior + 1,
    inputTape := ({ Tape.ofBits (false :: tail) with left := beforeInput }).write
      (some (prior == Ordering.lt)),
    outputTape := { Tape.ofBits output with left := beforeOutput }, halted := true }

private theorem pair (prior : Ordering) (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus : Bool) (input output : List Bool) :
    evalConfigWithin program
      (state prior beforeInput beforeOutput
        (true :: candidate :: input) (modulus :: output)) 7 =
      PMF.pure (state (BinaryComparison.update prior candidate modulus)
        (some candidate :: some true :: beforeInput)
        (some modulus :: beforeOutput) input output) := by
  cases prior <;> cases candidate <;> cases modulus <;>
    cases input <;> cases output <;>
    simp [evalConfigWithin, stepPMF, next, program, block, state,
      address, finishAddress, BinaryComparison.update, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape,
      Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem end_field (prior : Ordering)
    (beforeInput beforeOutput : List (Option Bool))
    (tail output : List Bool) :
    evalConfigWithin program
      (state prior beforeInput beforeOutput (false :: tail) output) 3 =
      PMF.pure (done prior beforeInput beforeOutput tail output) := by
  cases prior <;> cases tail <;> cases output <;>
    simp [evalConfigWithin, stepPMF, next, program, block, state,
      address, finishAddress, done, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape,
      Tape.ofBits, Tape.write, PMF.pure_bind]

/-- A matching-width pair leaves the same numerical comparison as the
existing interleaved-input comparator. No mathematical comparison is a
machine instruction in this proof. -/
theorem eval_equal_width (prior : Ordering)
    (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    ∃ finish,
      evalConfigWithin program
        (state prior beforeInput beforeOutput
          (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
        (7 * candidate.length + 3) = PMF.pure finish ∧
      finish.halted = true ∧
      finish.inputTape.current =
        some (BinaryComparison.compare prior (candidate.zip modulus) == Ordering.lt) := by
  induction candidate generalizing prior beforeInput beforeOutput modulus with
  | nil =>
      cases modulus with
      | nil =>
          refine ⟨done prior beforeInput beforeOutput tail suffix, ?_, rfl, ?_⟩
          · simpa [FiniteBitEncoding.delimit] using
              end_field prior beforeInput beforeOutput tail suffix
          · simp [done, Tape.write, BinaryComparison.compare]
      | cons bit rest => simp at hWidth
  | cons bit rest ih =>
      cases modulus with
      | nil => simp at hWidth
      | cons modulusBit modulusRest =>
          have hRest : rest.length = modulusRest.length := by
            simpa using hWidth
          obtain ⟨finish, hEval, hHalt, hStatus⟩ := ih
            (BinaryComparison.update prior bit modulusBit)
            (some bit :: some true :: beforeInput)
            (some modulusBit :: beforeOutput) modulusRest hRest
          refine ⟨finish, ?_, hHalt, ?_⟩
          · have hBudget : 7 * (bit :: rest).length + 3 =
                7 + (7 * rest.length + 3) := by simp; omega
            rw [hBudget, evalConfigWithin_add]
            simpa only [FiniteBitEncoding.delimit, List.cons_append,
              List.cons_append, pair, PMF.pure_bind] using hEval
          · simpa [BinaryComparison.compare] using hStatus

/-- From the equal initial comparison state, the bit written at the
candidate delimiter is exactly the numerical less-than decision. -/
theorem eval_lt (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    ∃ finish,
      evalConfigWithin program
        (state Ordering.eq beforeInput beforeOutput
          (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
        (7 * candidate.length + 3) = PMF.pure finish ∧
      finish.halted = true ∧
      finish.inputTape.current =
        some (decide (Binary.value candidate < Binary.value modulus)) := by
  obtain ⟨finish, hEval, hHalt, hStatus⟩ :=
    eval_equal_width Ordering.eq beforeInput beforeOutput
      candidate modulus tail suffix hWidth
  refine ⟨finish, hEval, hHalt, ?_⟩
  rw [hStatus, BinaryComparison.compare_values]
  rw [List.map_fst_zip (by omega : candidate.length ≤ modulus.length),
    List.map_snd_zip (by omega : modulus.length ≤ candidate.length)]
  by_cases h : Binary.value candidate < Binary.value modulus
  · simp [h]
  · simp [h]
    split_ifs <;> decide

/-- The marker/payload cells preceding one delimiter. -/
def marked : List Bool → List Bool
  | [] => []
  | bit :: rest => true :: bit :: marked rest

theorem delimit_eq_marked (bits : List Bool) :
    FiniteBitEncoding.delimit bits = marked bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [FiniteBitEncoding.delimit, marked, ih]

/-- The exact physical tapes after a successful equal-width comparison.
The modulus and all following output cells are retained; the input
delimiter contains the decision bit. -/
theorem eval_equal_width_layout (prior : Ordering)
    (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    evalConfigWithin program
      (state prior beforeInput beforeOutput
        (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
      (7 * candidate.length + 3) =
      PMF.pure (done (BinaryComparison.compare prior (candidate.zip modulus))
        ((marked candidate).reverse.map some ++ beforeInput)
        (modulus.reverse.map some ++ beforeOutput) tail suffix) := by
  induction candidate generalizing prior beforeInput beforeOutput modulus with
  | nil =>
      cases modulus with
      | nil => simpa [marked, BinaryComparison.compare, FiniteBitEncoding.delimit]
          using end_field prior beforeInput beforeOutput tail suffix
      | cons bit rest => simp at hWidth
  | cons bit rest ih =>
      cases modulus with
      | nil => simp at hWidth
      | cons modulusBit modulusRest =>
          have hRest : rest.length = modulusRest.length := by
            simpa using hWidth
          have hBudget : 7 * (bit :: rest).length + 3 =
              7 + (7 * rest.length + 3) := by simp; omega
          rw [hBudget, evalConfigWithin_add]
          simp only [FiniteBitEncoding.delimit, List.cons_append,
            pair, PMF.pure_bind]
          simpa [BinaryComparison.compare, marked, List.reverse_append,
            List.map_append, List.append_assoc] using
            ih (BinaryComparison.update prior bit modulusBit)
              (some bit :: some true :: beforeInput)
              (some modulusBit :: beforeOutput) modulusRest hRest

private theorem pair_any (prior : Ordering) (input output : Tape)
    (candidate modulus : Bool)
    (hMarker : input.current = some true)
    (hPayload : input.moveRight.current = some candidate)
    (hModulus : output.current = some modulus) :
    evalConfigWithin program (atState prior input output) 7 =
      PMF.pure (atState (BinaryComparison.update prior candidate modulus)
        input.moveRight.moveRight output.moveRight) := by
  cases prior <;> cases candidate <;> cases modulus <;>
    simp [evalConfigWithin, stepPMF, next, program, block, atState,
      address, finishAddress, BinaryComparison.update, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape,
      hMarker, hPayload, hModulus, PMF.pure_bind]

private theorem terminal_marker (prior : Ordering) (input output : Tape)
    (hMarker : input.current = none ∨ input.current = some false) :
    ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output) 7 = PMF.pure finish := by
  rcases hMarker with hBlank | hDelimiter
  · cases prior <;>
      simp [evalConfigWithin, stepPMF, next, program, block, atState,
        address, finishAddress, hBlank, Instruction.next,
        Configuration.advance, Configuration.tape, Configuration.updateTape,
        Tape.write, PMF.pure_bind] <;> exact ⟨_, rfl, rfl⟩
  · cases prior <;>
      simp [evalConfigWithin, stepPMF, next, program, block, atState,
        address, finishAddress, hDelimiter, Instruction.next,
        Configuration.advance, Configuration.tape, Configuration.updateTape,
        Tape.write, PMF.pure_bind] <;> exact ⟨_, rfl, rfl⟩

private theorem terminal_payload (prior : Ordering) (input output : Tape)
    (hMarker : input.current = some true)
    (hPayload : input.moveRight.current = none) :
    ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output) 7 = PMF.pure finish := by
  cases prior <;>
    simp [evalConfigWithin, stepPMF, next, program, block, atState,
      address, finishAddress, hMarker, hPayload, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape,
      Tape.write, PMF.pure_bind] <;> exact ⟨_, rfl, rfl⟩

private theorem terminal_modulus (prior : Ordering) (input output : Tape)
    (candidate : Bool)
    (hMarker : input.current = some true)
    (hPayload : input.moveRight.current = some candidate)
    (hModulus : output.current = none) :
    ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output) 7 = PMF.pure finish := by
  cases prior <;> cases candidate <;>
    simp [evalConfigWithin, stepPMF, next, program, block, atState,
      address, finishAddress, hMarker, hPayload, hModulus, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape,
      Tape.write, PMF.pure_bind] <;> exact ⟨_, rfl, rfl⟩

private theorem eval_halted (finish : Configuration) (steps : Nat)
    (hHalt : finish.halted = true) :
    evalConfigWithin program finish steps = PMF.pure finish := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, hHalt]

private theorem terminal_budget (prior : Ordering) (input output : Tape)
    (h : ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output) 7 = PMF.pure finish) :
    ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output)
        (7 * (input.right.length + 1)) = PMF.pure finish := by
  obtain ⟨finish, hHalt, hEval⟩ := h
  refine ⟨finish, hHalt, ?_⟩
  have hBudget : 7 * (input.right.length + 1) = 7 + 7 * input.right.length := by omega
  rw [hBudget, evalConfigWithin_add, hEval, PMF.pure_bind]
  exact eval_halted finish _ hHalt

/-- From any finite retained input and modulus tapes, the same finite code
halts within a linear bound. Missing markers, truncated payloads, and a
short modulus take rejecting branches. -/
theorem terminates_from_anyTape (prior : Ordering) (input output : Tape) :
    ∃ finish, finish.halted = true ∧
      evalConfigWithin program (atState prior input output)
        (7 * (input.right.length + 1)) = PMF.pure finish := by
  cases hMarker : input.current with
  | none =>
      exact terminal_budget prior input output
        (terminal_marker prior input output (Or.inl hMarker))
  | some marker =>
      cases marker with
      | false =>
          exact terminal_budget prior input output
            (terminal_marker prior input output (Or.inr hMarker))
      | true =>
          cases hPayload : input.moveRight.current with
          | none =>
              exact terminal_budget prior input output
                (terminal_payload prior input output hMarker hPayload)
          | some candidate =>
              cases hModulus : output.current with
              | none =>
                  exact terminal_budget prior input output
                    (terminal_modulus prior input output candidate
                      hMarker hPayload hModulus)
              | some modulus =>
                  obtain ⟨finish, hHalt, hEval⟩ :=
                    terminates_from_anyTape
                      (BinaryComparison.update prior candidate modulus)
                      input.moveRight.moveRight output.moveRight
                  refine ⟨finish, hHalt, ?_⟩
                  have hLength :
                      (input.moveRight.moveRight).right.length + 1 ≤
                        input.right.length := by
                    cases input with
                    | mk left current right =>
                        cases right with
                        | nil => simp [Tape.moveRight] at hPayload
                        | cons cell rest =>
                            cases cell with
                            | none => simp [Tape.moveRight] at hPayload
                            | some bit =>
                                cases rest <;>
                                  simp [Tape.moveRight]
                  have hUsed :
                      7 + 7 * ((input.moveRight.moveRight).right.length + 1) ≤
                        7 * (input.right.length + 1) := by omega
                  have hBudget : 7 * (input.right.length + 1) =
                      (7 + 7 * ((input.moveRight.moveRight).right.length + 1)) +
                        (7 * (input.right.length + 1) -
                          (7 + 7 * ((input.moveRight.moveRight).right.length + 1))) := by
                    omega
                  have hFirst : evalConfigWithin program (atState prior input output)
                      (7 + 7 * ((input.moveRight.moveRight).right.length + 1)) =
                        PMF.pure finish := by
                    rw [evalConfigWithin_add,
                      pair_any prior input output candidate modulus
                        hMarker hPayload hModulus,
                      PMF.pure_bind]
                    exact hEval
                  rw [hBudget, evalConfigWithin_add, hFirst, PMF.pure_bind]
                  exact eval_halted finish _ hHalt
termination_by input.right.length
decreasing_by
  cases input with
  | mk left current right =>
      cases right with
      | nil => simp [Tape.moveRight] at hPayload
      | cons cell rest =>
          cases cell with
          | none => simp [Tape.moveRight] at hPayload
          | some bit =>
              cases rest <;> simp_all [Tape.moveRight]

/-- The stopped evaluator trace can be embedded as an actual, unpadded
trace on the same tapes. -/
theorem runs_from_anyTape (prior : Ordering) (input output : Tape) :
    ∃ finish used, used ≤ 7 * (input.right.length + 1) ∧
      RunsFor program (atState prior input output) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, hHalt, hEval⟩ :=
    terminates_from_anyTape prior input output
  have hSupport : finish ∈
      (evalConfigWithin program (atState prior input output)
        (7 * (input.right.length + 1))).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨finish, used, hUsed, run, hHalt⟩

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- The fixed comparator is total on arbitrary finite input, including
truncated fields and short or blank modulus tapes. -/
theorem haltsWithin (raw : List Bool) :
    HaltsWithin program raw (7 * (raw.length + 1)) := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ :=
    runs_from_anyTape Ordering.eq (Tape.ofBits raw) ({} : Tape)
  have hInitial : Configuration.initial raw =
      atState Ordering.eq (Tape.ofBits raw) ({} : Tape) := by
    cases raw <;> rfl
  rw [← hInitial] at run
  have hLength : (Tape.ofBits raw).right.length ≤ raw.length := by
    cases raw <;> simp [Tape.ofBits]
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit (by omega)

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 7 * (length + 1),
    (PolynomiallyBounded.const 7).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)),
    haltsWithin⟩

/-- The numerical decision also has an actual finite operational trace,
so callers can embed this comparator as a subroutine on retained tapes. -/
theorem runs_lt (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    ∃ finish used,
      used ≤ 7 * candidate.length + 3 ∧
      RunsFor program
        (state Ordering.eq beforeInput beforeOutput
          (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
        finish used ∧
      finish.halted = true ∧
      finish.inputTape.current =
        some (decide (Binary.value candidate < Binary.value modulus)) := by
  obtain ⟨finish, hEval, hHalt, hStatus⟩ :=
    eval_lt beforeInput beforeOutput candidate modulus tail suffix hWidth
  have hSupport : finish ∈
      (evalConfigWithin program
        (state Ordering.eq beforeInput beforeOutput
          (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
        (7 * candidate.length + 3)).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨finish, used, hUsed, run, hHalt, hStatus⟩

/-- The operational trace exposes the retained suffix and the exact head
locations needed to continue with another finite-code validation stage. -/
theorem runs_lt_layout (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    ∃ used, used ≤ 7 * candidate.length + 3 ∧
      RunsFor program
        (state Ordering.eq beforeInput beforeOutput
          (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
        (done (BinaryComparison.compare Ordering.eq (candidate.zip modulus))
          ((marked candidate).reverse.map some ++ beforeInput)
          (modulus.reverse.map some ++ beforeOutput) tail suffix) used := by
  have hEval := eval_equal_width_layout Ordering.eq beforeInput beforeOutput
    candidate modulus tail suffix hWidth
  have hSupport :
      done (BinaryComparison.compare Ordering.eq (candidate.zip modulus))
          ((marked candidate).reverse.map some ++ beforeInput)
          (modulus.reverse.map some ++ beforeOutput) tail suffix ∈
        (evalConfigWithin program
          (state Ordering.eq beforeInput beforeOutput
            (FiniteBitEncoding.delimit candidate ++ tail) (modulus ++ suffix))
          (7 * candidate.length + 3)).support := by
    rw [hEval]
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le

theorem done_lt_status (beforeInput beforeOutput : List (Option Bool))
    (candidate modulus tail suffix : List Bool)
    (hWidth : candidate.length = modulus.length) :
    (done (BinaryComparison.compare Ordering.eq (candidate.zip modulus))
      ((marked candidate).reverse.map some ++ beforeInput)
      (modulus.reverse.map some ++ beforeOutput) tail suffix).inputTape.current =
        some (decide (Binary.value candidate < Binary.value modulus)) := by
  simp only [done, Tape.write]
  rw [BinaryComparison.compare_values,
    List.map_fst_zip (by omega : candidate.length ≤ modulus.length),
    List.map_snd_zip (by omega : modulus.length ≤ candidate.length)]
  by_cases h : Binary.value candidate < Binary.value modulus
  · simp [h]
  · simp [h]
    split_ifs <;> decide

end Machine.DelimitedTapeComparison
