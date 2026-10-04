import Foundation.Machine.FiniteRandomness
import Foundation.Machine.BinaryComparison
import Foundation.Machine.BitstringRewind
import Foundation.Machine.SavedBitstringRewind

namespace Machine.RejectionSampling

/-- One fixed finite program for a positive, canonical little-endian binary
modulus on the input tape. Validation rejects the empty string and a zero
most-significant bit. A trial generates one output bit per input bit and
compares the candidate with the modulus, remembering the comparison in finite
control. Rejected trials rewind both physical heads and retry. No numerical
operation or whole-string sampler is a machine instruction.

This definition supplies the code. Its parameterized distribution and
expected-time certificates are separate proof obligations. -/
private def retryBody : Program :=
  [-- Validate that the last input bit is one.
   .branch .input 42 1 4,              -- 0
   .moveRight .input,                  -- 1: last bit zero
   .branch .input 42 1 4,              -- 2
   .jump 42,                          -- 3: unused
   .moveRight .input,                  -- 4: last bit one
   .branch .input 6 1 4,               -- 5
   .moveLeft .input,                   -- 6: rewind validated input
   .branch .input 8 6 6,               -- 7
   .moveRight .input,                  -- 8
   .jump 10,                          -- 9
   -- Candidate equal to the modulus in the lower bits inspected so far.
   .branch .input 34 11 11,            -- 10
   .randomBit .output,                 -- 11
   .branch .input 42 13 14,            -- 12
   .branch .output 42 25 31,           -- 13
   .branch .output 42 28 25,           -- 14
   -- Candidate less than the modulus in the inspected lower bits.
   .branch .input 41 16 16,            -- 15
   .randomBit .output,                 -- 16
   .branch .input 42 18 19,            -- 17
   .branch .output 42 28 31,           -- 18
   .branch .output 42 28 28,           -- 19
   -- Candidate greater than the modulus in the inspected lower bits.
   .branch .input 34 21 21,            -- 20
   .randomBit .output,                 -- 21
   .branch .input 42 23 24,            -- 22
   .branch .output 42 31 31,           -- 23
   .branch .output 42 28 31,           -- 24
   -- Advance both heads, retaining the finite comparison state.
   .moveRight .input, .moveRight .output, .jump 10, -- 25--27
   .moveRight .input, .moveRight .output, .jump 15, -- 28--30
   .moveRight .input, .moveRight .output, .jump 20, -- 31--33
   -- Rewind after rejection; old candidate cells are overwritten next trial.
   .moveLeft .input, .moveLeft .output, .branch .input 37 34 34, -- 34--36
   .moveRight .input, .moveRight .output, .jump 10, -- 37--39
   .halt,                             -- 40: unused
   .halt,                             -- 41: accepted candidate
   .halt]                             -- 42: malformed input

private def offset : Instruction → Instruction
  | .branch tape blank zeroPc onePc => .branch tape (blank + 7) (zeroPc + 7) (onePc + 7)
  | .jump pc => .jump (pc + 7)
  | instruction => instruction

/-- A deterministic `q=1` fast path precedes the general retry code. The
single possible scalar is returned without reading any random bits. -/
def program : Program :=
  [.branch .input 49 7 1, .moveRight .input, .branch .input 3 5 5,
   .write .output false, .halt, .moveLeft .input, .jump 7] ++ retryBody.map offset

theorem one_haltsWithin : HaltsWithin program [true] 5 := by
  rw [haltsWithin_iff_reachableStates]
  decide

theorem one_eval : evalWithin program [true] 5 = PMF.pure (some [false]) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, program, retryBody, offset,
    Instruction.next, Configuration.initial, Configuration.advance,
    Configuration.updateTape, Configuration.tape, Configuration.outputBits,
    Tape.ofBits, Tape.moveRight, Tape.write, Tape.bits, PMF.pure_bind, PMF.pure_map]

private def validationState (last : Bool) (before : List (Option Bool))
    (remaining : List Bool) : Configuration :=
  { pc := if last then 12 else 9,
    inputTape := { Tape.ofBits remaining with left := before } }

private def lastSeen : Bool → List Bool → Bool
  | last, [] => last
  | _, bit :: rest => lastSeen bit rest

private theorem eval_validation_bit (last bit : Bool) (before : List (Option Bool))
    (rest : List Bool) :
    evalConfigWithin program (validationState last before (bit :: rest)) 2 =
      PMF.pure (validationState bit (some bit :: before) rest) := by
  cases last <;> cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
      validationState, Instruction.next, Configuration.advance,
      Configuration.updateTape, Configuration.tape, Tape.ofBits,
      Tape.moveRight, PMF.pure_bind]

private theorem eval_validation (bits : List Bool) (last : Bool)
    (before : List (Option Bool)) :
    evalConfigWithin program (validationState last before bits) (2 * bits.length + 1) =
      PMF.pure ({
        pc := if lastSeen last bits then 13 else 49,
        inputTape := { left := bits.reverse.map some ++ before } } : Configuration) := by
  induction bits generalizing last before with
  | nil =>
      cases last <;>
        simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
          validationState, lastSeen, Instruction.next, Configuration.tape, Tape.ofBits,
          PMF.pure_bind]
  | cons bit rest ih =>
      have hBudget : 2 * (bit :: rest).length + 1 = 2 + (2 * rest.length + 1) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_validation_bit, PMF.pure_bind, ih]
      simp [lastSeen, List.reverse_cons, List.map_append, List.append_assoc]
      rfl

private theorem lastSeen_zero (last : Bool) (leading : List Bool) :
    lastSeen last (leading ++ [false]) = false := by
  induction leading generalizing last with
  | nil => rfl
  | cons bit rest ih => exact ih bit

def validationStart (bits : List Bool) : Configuration :=
  { pc := 7, inputTape := Tape.ofBits bits }

private theorem eval_validation_start (bits : List Bool) (steps : Nat) :
    evalConfigWithin program (validationStart bits) (steps + 1) =
      evalConfigWithin program (validationState false [] bits) (steps + 1) := by
  rw [evalConfigWithin_succ_head, evalConfigWithin_succ_head]
  congr 1
  cases bits with
  | nil => simp [stepPMF, next, program, retryBody, offset, validationStart,
      validationState, Instruction.next, Tape.ofBits, Configuration.tape]
  | cons bit rest => cases bit <;>
      simp [stepPMF, next, program, retryBody, offset, validationStart,
        validationState, Instruction.next, Tape.ofBits, Configuration.tape]

theorem eval_guard_false (rest : List Bool) :
    evalConfigWithin program (Configuration.initial (false :: rest)) 1 =
      PMF.pure (validationStart (false :: rest)) := by
  simp [evalConfigWithin, stepPMF, next, program, validationStart,
    Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
    PMF.pure_bind]

theorem eval_guard_true (bit : Bool) (rest : List Bool) :
    evalConfigWithin program (Configuration.initial (true :: bit :: rest)) 5 =
      PMF.pure (validationStart (true :: bit :: rest)) := by
  cases bit <;> simp [evalConfigWithin, stepPMF, next, program, validationStart,
    Configuration.initial, Tape.ofBits, Tape.moveRight, Tape.moveLeft, Instruction.next,
    Configuration.tape, Configuration.advance, Configuration.updateTape, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_invalid_body (leading : List Bool) :
    evalConfigWithin program (validationStart (leading ++ [false]))
        (2 * (leading ++ [false]).length + 2) =
      PMF.pure ({
        pc := 49, inputTape := { left := (leading ++ [false]).reverse.map some },
        halted := true } : Configuration) := by
  rw [show 2 * (leading ++ [false]).length + 2 =
    (2 * (leading ++ [false]).length + 1) + 1 by omega,
    evalConfigWithin_add, eval_validation_start, eval_validation, PMF.pure_bind]
  simp [lastSeen_zero, evalConfigWithin, stepPMF, next, program, retryBody, offset,
    Instruction.next, PMF.pure_bind]

/-- Every nonempty input with a zero most-significant bit is rejected before
any random instruction executes. The same bound holds for all such inputs. -/
theorem malformed_eval (leading : List Bool) :
    evalConfigWithin program (Configuration.initial (leading ++ [false]))
        (2 * (leading ++ [false]).length + 8) =
      PMF.pure ({
        pc := 49, inputTape := { left := (leading ++ [false]).reverse.map some },
        halted := true } : Configuration) := by
  cases leading with
  | nil =>
      change evalConfigWithin program (Configuration.initial [false])
        (1 + (2 * [false].length + 2 + 5)) = _
      rw [evalConfigWithin_add, eval_guard_false, PMF.pure_bind, evalConfigWithin_add]
      have hBody := eval_invalid_body []
      simp only [List.nil_append] at hBody
      rw [hBody, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | cons first rest =>
      cases first with
      | false =>
          have hBudget : 2 * ((false :: rest) ++ [false]).length + 8 =
              1 + (2 * ((false :: rest) ++ [false]).length + 2 + 5) := by omega
          rw [hBudget, evalConfigWithin_add]
          simp only [List.cons_append, eval_guard_false, PMF.pure_bind]
          rw [evalConfigWithin_add]
          have hBody := eval_invalid_body (false :: rest)
          simp only [List.cons_append] at hBody
          rw [hBody, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | true =>
          have hNonempty : rest ++ [false] ≠ [] := by simp
          cases hRest : rest ++ [false] with
          | nil => exact False.elim (hNonempty hRest)
          | cons bit tail =>
              have hBudget : 2 * ((true :: rest) ++ [false]).length + 8 =
                  5 + (2 * ((true :: rest) ++ [false]).length + 2 + 1) := by omega
              rw [hBudget, evalConfigWithin_add]
              simp only [List.cons_append, hRest, eval_guard_true, PMF.pure_bind]
              rw [evalConfigWithin_add]
              have hBody := eval_invalid_body (true :: rest)
              simp only [List.cons_append, hRest] at hBody
              rw [hBody, PMF.pure_bind]
              exact eval_halted _ _ rfl

theorem malformed_haltsWithin (leading : List Bool) :
    HaltsWithin program (leading ++ [false]) (2 * (leading ++ [false]).length + 8) := by
  intro finish run
  have hSupport := (mem_support_evalConfigWithin_iff program _ finish _).mpr run
  rw [malformed_eval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ rfl

private def rewindState (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) : Configuration :=
  { pc := 13, inputTape := { left := left.map some, current := current, right := right } }

private def rewindFinish (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) : Configuration :=
  { pc := 17, inputTape := ({ right := left.reverse.map some ++ current :: right } : Tape).moveRight }

private theorem eval_validation_rewind (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) :
    evalConfigWithin program (rewindState left current right) (2 * left.length + 4) =
      PMF.pure (rewindFinish left current right) := by
  induction left generalizing current right with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
        rewindState, rewindFinish, Instruction.next, Configuration.tape,
        Configuration.advance, Configuration.updateTape, Tape.moveLeft,
        Tape.moveRight, PMF.pure_bind]
  | cons bit rest ih =>
      have hBudget : 2 * (bit :: rest).length + 4 = 2 + (2 * rest.length + 4) := by simp; omega
      have hPair : evalConfigWithin program (rewindState (bit :: rest) current right) 2 =
          PMF.pure (rewindState rest (some bit) (current :: right)) := by
        cases bit <;>
          simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
            rewindState, Instruction.next, Configuration.tape,
            Configuration.advance, Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]
      rw [hBudget, evalConfigWithin_add, hPair, PMF.pure_bind, ih]
      simp [rewindFinish, List.reverse_cons, List.map_append, List.append_assoc]

private theorem lastSeen_one (last : Bool) (leading : List Bool) :
    lastSeen last (leading ++ [true]) = true := by
  induction leading generalizing last with
  | nil => rfl
  | cons bit rest ih => exact ih bit

/-- Physical input layout after validation and the charged rewind. Extra
outer blank cells remain in the tape representation. -/
def validatedTrialStart (bits : List Bool) : Configuration :=
  { pc := 17, inputTape := ({ right := bits.map some ++ [none] } : Tape).moveRight }

/-- The validator and rewind execute four transitions per input bit plus
five fixed transitions. This certificate starts at the validator's actual
entry address; the public `q=1` guard precedes that address. -/
theorem eval_validateBody (leading : List Bool) :
    let bits := leading ++ [true]
    evalConfigWithin program (validationStart bits) (4 * bits.length + 5) =
      PMF.pure (validatedTrialStart bits) := by
  dsimp only
  have hBudget : 4 * (leading ++ [true]).length + 5 =
      (2 * (leading ++ [true]).length + 1) + (2 * (leading ++ [true]).length + 4) := by omega
  rw [hBudget, evalConfigWithin_add, eval_validation_start, eval_validation, PMF.pure_bind]
  simp only [lastSeen_one, ↓reduceIte, List.append_nil]
  have hRewind := eval_validation_rewind (leading ++ [true]).reverse none []
  simpa [rewindState, rewindFinish, validatedTrialStart] using hRewind

/-- The layout equivalence preserves every tape cell; it is not an extra
normalization step or an assumption that preparing input is free. -/
theorem validatedTrialStart_input_equivalent (bits : List Bool) :
    (validatedTrialStart bits).inputTape.Equivalent (Tape.ofBits bits) :=
  rewindBitstringFinish_input_equivalent bits {}

theorem validatedTrialStart_equivalent (bits : List Bool) :
    (validatedTrialStart bits).Equivalent
      ({ pc := 17, inputTape := Tape.ofBits bits } : Configuration) :=
  ⟨rfl, rfl, validatedTrialStart_input_equivalent bits, Tape.Equivalent.refl _⟩

private def rejectRewindState (left : List (Bool × Bool))
    (inputCurrent outputCurrent : Option Bool)
    (inputRight outputRight : List (Option Bool)) : Configuration :=
  { pc := 41,
    inputTape := {
      left := (left.map Prod.fst).map some
      current := inputCurrent
      right := inputRight },
    outputTape := {
      left := (left.map Prod.snd).map some
      current := outputCurrent
      right := outputRight } }

private def rejectRewindFinish (left : List (Bool × Bool))
    (inputCurrent outputCurrent : Option Bool)
    (inputRight outputRight : List (Option Bool)) : Configuration :=
  { pc := 17,
    inputTape := ({ right := (left.map Prod.fst).reverse.map some ++
      inputCurrent :: inputRight } : Tape).moveRight,
    outputTape := ({ right := (left.map Prod.snd).reverse.map some ++
      outputCurrent :: outputRight } : Tape).moveRight }

private theorem eval_rejectRewind (left : List (Bool × Bool))
    (inputCurrent outputCurrent : Option Bool)
    (inputRight outputRight : List (Option Bool)) :
    evalConfigWithin program
        (rejectRewindState left inputCurrent outputCurrent inputRight outputRight)
        (3 * left.length + 6) =
      PMF.pure (rejectRewindFinish left inputCurrent outputCurrent inputRight outputRight) := by
  induction left generalizing inputCurrent outputCurrent inputRight outputRight with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
        rejectRewindState, rejectRewindFinish, Instruction.next, Configuration.tape,
        Configuration.advance, Configuration.updateTape, Tape.moveLeft,
        Tape.moveRight, PMF.pure_bind]
  | cons pair rest ih =>
      rcases pair with ⟨inputBit, outputBit⟩
      have hBudget : 3 * ((inputBit, outputBit) :: rest).length + 6 =
          3 + (3 * rest.length + 6) := by simp; omega
      have hTriple : evalConfigWithin program
          (rejectRewindState ((inputBit, outputBit) :: rest) inputCurrent outputCurrent
            inputRight outputRight) 3 =
          PMF.pure (rejectRewindState rest (some inputBit) (some outputBit)
            (inputCurrent :: inputRight) (outputCurrent :: outputRight)) := by
        cases inputBit <;>
          simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
            rejectRewindState, Instruction.next, Configuration.tape,
            Configuration.advance, Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]
      rw [hBudget, evalConfigWithin_add, hTriple, PMF.pure_bind, ih]
      simp [rejectRewindFinish, List.reverse_cons, List.map_append, List.append_assoc]

private def scanAddress : Ordering → Nat
  | .eq => 17
  | .lt => 22
  | .gt => 27

private def cells (before after : List (Option Bool)) : Tape :=
  match after with
  | [] => { left := before }
  | cell :: rest => { left := before, current := cell, right := rest }

private def scanState (prior : Ordering) (before : List (Option Bool))
    (remaining : List Bool) (written old : List (Option Bool)) : Configuration :=
  { pc := scanAddress prior,
    inputTape := { Tape.ofBits remaining with left := before },
    outputTape := cells written old }

set_option maxHeartbeats 1200000 in
private theorem eval_scan_bit (prior : Ordering) (before written old : List (Option Bool))
    (modulusBit : Bool) (rest : List Bool) :
    evalConfigWithin program (scanState prior before (modulusBit :: rest) written old) 7 =
      Foundation.Probability.sampleBit.map (fun bit =>
        scanState (BinaryComparison.update prior bit modulusBit)
          (some modulusBit :: before) rest (some bit :: written) old.tail) := by
  cases prior <;> cases modulusBit <;> cases rest <;> cases old <;>
    simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
      scanState, scanAddress, cells, Instruction.next, Configuration.advance,
      Configuration.updateTape, Configuration.tape, Tape.ofBits, Tape.moveRight,
      Tape.write, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  all_goals
    conv_rhs => rw [← PMF.bind_pure_comp]
    congr 1
    funext bit
    cases bit <;> simp [BinaryComparison.update, stepPMF, next,
      Instruction.next, PMF.pure_bind]
  all_goals rfl

private theorem eval_scan (modulus : List Bool) (prior : Ordering)
    (before written old : List (Option Bool)) :
    evalConfigWithin program (scanState prior before modulus written old)
        (7 * modulus.length) =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map (fun bits =>
        scanState (BinaryComparison.compare prior ((List.ofFn bits).zip modulus))
          (modulus.reverse.map some ++ before) []
          ((List.ofFn bits).reverse.map some ++ written) (old.drop modulus.length)) := by
  induction modulus generalizing prior before written old with
  | nil => simp [evalConfigWithin, BinaryComparison.compare, PMF.map_const, Function.const_def]
  | cons modulusBit rest ih =>
      have hBudget : 7 * (modulusBit :: rest).length = 7 + 7 * rest.length := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_scan_bit, PMF.bind_map]
      simp only [Function.comp_def, ih]
      simp only [List.length_cons]
      rw [← uniform_bits_cons, PMF.map_bind]
      congr 1
      funext bit
      simp only [PMF.map_comp, Function.comp_def, List.ofFn_cons, List.zip_cons_cons,
        BinaryComparison.compare, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.singleton_append, List.append_assoc]
      congr 1
      funext bits
      congr 1
      simp [List.drop_tail]

/-- Start of the candidate-generation loop, after modulus validation and
head restoration. Preparation is not treated as a free machine transition. -/
def trialStart (modulus previous : List Bool) : Configuration :=
  { pc := 17, inputTape := Tape.ofBits modulus, outputTape := Tape.ofBits previous }

/-- The physical configuration after scanning a candidate. Acceptance,
rejection, and rewinding have not yet executed. -/
def candidateFinish (modulus previous : List Bool) (bits : Fin modulus.length → Bool) : Configuration :=
  scanState (BinaryComparison.compare .eq ((List.ofFn bits).zip modulus))
    (modulus.reverse.map some) [] ((List.ofFn bits).reverse.map some)
    ((previous.map some).drop modulus.length)

private def endState (prior : Ordering) (modulus candidate : List Bool) : Configuration :=
  { pc := scanAddress prior,
    inputTape := { left := modulus.reverse.map some },
    outputTape := { left := candidate.reverse.map some } }

private def accepted (modulus candidate : List Bool) : Configuration :=
  { pc := 48, inputTape := { left := modulus.reverse.map some },
    outputTape := { left := candidate.reverse.map some }, halted := true }

private def retryStart (modulus candidate : List Bool) : Configuration :=
  { pc := 17,
    inputTape := ({ right := modulus.map some ++ [none] } : Tape).moveRight,
    outputTape := ({ right := candidate.map some ++ [none] } : Tape).moveRight }

private theorem eval_trialTail (prior : Ordering) (modulus candidate : List Bool)
    (hLength : candidate.length = modulus.length) :
    evalConfigWithin program (endState prior modulus candidate) (3 * modulus.length + 7) =
      PMF.pure (if prior = .lt then accepted modulus candidate else retryStart modulus candidate) := by
  have hFirst : (modulus.zip candidate).map Prod.fst = modulus :=
    List.map_fst_zip (by omega)
  have hSecond : (modulus.zip candidate).map Prod.snd = candidate :=
    List.map_snd_zip (by omega)
  have hRewind : evalConfigWithin program
      ({
        pc := 41
        inputTape := { left := modulus.reverse.map some }
        outputTape := { left := candidate.reverse.map some } } : Configuration)
      (3 * modulus.length + 6) = PMF.pure (retryStart modulus candidate) := by
    simpa [rejectRewindState, rejectRewindFinish, retryStart, List.map_reverse,
      hFirst, hSecond, List.length_zip, hLength] using
      eval_rejectRewind (modulus.zip candidate).reverse none none [] []
  cases prior with
  | eq =>
      have hStep : evalConfigWithin program (endState .eq modulus candidate) 1 =
          PMF.pure ({
            pc := 41
            inputTape := { left := modulus.reverse.map some }
            outputTape := { left := candidate.reverse.map some } } : Configuration) := by
        simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
          endState, scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
      rw [show 3 * modulus.length + 7 = 1 + (3 * modulus.length + 6) by omega,
        evalConfigWithin_add, hStep, PMF.pure_bind, hRewind]
      simp
  | lt =>
      have hStep : evalConfigWithin program (endState .lt modulus candidate) 2 =
          PMF.pure (accepted modulus candidate) := by
        simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
          endState, accepted, scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
      rw [show 3 * modulus.length + 7 = 2 + (3 * modulus.length + 5) by omega,
        evalConfigWithin_add, hStep, PMF.pure_bind, eval_halted _ _ rfl]
      simp
  | gt =>
      have hStep : evalConfigWithin program (endState .gt modulus candidate) 1 =
          PMF.pure ({
            pc := 41
            inputTape := { left := modulus.reverse.map some }
            outputTape := { left := candidate.reverse.map some } } : Configuration) := by
        simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
          endState, scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
      rw [show 3 * modulus.length + 7 = 1 + (3 * modulus.length + 6) by omega,
        evalConfigWithin_add, hStep, PMF.pure_bind, hRewind]
      simp

/-- One trial either halts with its accepted candidate or returns both
physical heads to the next retry. The output's old cells are overwritten. -/
def trialResult (modulus : List Bool) (bits : Fin modulus.length → Bool) : Configuration :=
  if Binary.value (List.ofFn bits) < Binary.value modulus then
    accepted modulus (List.ofFn bits)
  else retryStart modulus (List.ofFn bits)

private theorem candidateFinish_tail (modulus previous : List Bool)
    (bits : Fin modulus.length → Bool) (hPrevious : previous.length ≤ modulus.length) :
    evalConfigWithin program (candidateFinish modulus previous bits) (3 * modulus.length + 7) =
      PMF.pure (trialResult modulus bits) := by
  have hDrop : (previous.map some).drop modulus.length = [] := by
    apply List.drop_eq_nil_iff.mpr
    simpa using hPrevious
  have hStart : candidateFinish modulus previous bits =
      endState (BinaryComparison.compare .eq ((List.ofFn bits).zip modulus)) modulus (List.ofFn bits) := by
    simp [candidateFinish, scanState, cells, hDrop, endState, Tape.ofBits]
  rw [hStart, eval_trialTail _ _ _ (by simp)]
  have hFirst := List.map_fst_zip (l₁ := List.ofFn bits) (l₂ := modulus) (by simp)
  have hSecond := List.map_snd_zip (l₁ := List.ofFn bits) (l₂ := modulus) (by simp)
  simp only [BinaryComparison.compare_values, hFirst, hSecond, trialResult]
  split_ifs <;> simp_all

/-- At seven actual transitions per modulus bit, the fixed retry code has
read independent fair bits and computed their exact comparison with `q`.
This is an operational scan certificate; the complete parser/retry expected-
time and limit-distribution theorems require the subsequent phases too. -/
theorem eval_candidateScan (modulus previous : List Bool) :
    evalConfigWithin program (trialStart modulus previous) (7 * modulus.length) =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map
        (candidateFinish modulus previous) := by
  have hStart : trialStart modulus previous = scanState .eq [] modulus [] (previous.map some) := by
    cases modulus <;> cases previous <;> rfl
  rw [hStart, eval_scan]
  congr 1
  funext bits
  simp only [List.append_nil, candidateFinish]

theorem candidateFinish_output (modulus previous : List Bool)
    (bits : Fin modulus.length → Bool) (h : previous.length ≤ modulus.length) :
    (candidateFinish modulus previous bits).outputBits = List.ofFn bits := by
  have hDrop : (previous.map some).drop modulus.length = [] := by
    apply List.drop_eq_nil_iff.mpr
    simpa using h
  simp [candidateFinish, scanState, cells, hDrop, Configuration.outputBits, Tape.bits,
    -List.map_ofFn]

theorem candidateFinish_comparison (modulus previous : List Bool)
    (bits : Fin modulus.length → Bool) :
    (candidateFinish modulus previous bits).pc = 22 ↔
      Binary.value (List.ofFn bits) < Binary.value modulus := by
  have hFirst : ((List.ofFn bits).zip modulus).map Prod.fst = List.ofFn bits :=
    List.map_fst_zip (by simp)
  have hSecond : ((List.ofFn bits).zip modulus).map Prod.snd = modulus :=
    List.map_snd_zip (by simp)
  simp only [candidateFinish, scanState, BinaryComparison.compare_values, hFirst, hSecond]
  split_ifs <;> simp_all [scanAddress]

/-- The emitted candidate is uniform over all width-many fair bits. This
statement is derived from the code's physical candidate-generation loop. -/
theorem candidateScan_output (modulus previous : List Bool)
    (h : previous.length ≤ modulus.length) :
    (evalConfigWithin program (trialStart modulus previous) (7 * modulus.length)).map
      Configuration.outputBits =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map List.ofFn := by
  rw [eval_candidateScan, PMF.map_comp]
  congr 1
  funext bits
  exact candidateFinish_output modulus previous bits h

/-- The actual candidate-generation loop samples each number below the
bit-width limit with the same probability, before rejection is applied. -/
theorem candidateScan_value (modulus previous : List Bool)
    (h : previous.length ≤ modulus.length) :
    ((evalConfigWithin program (trialStart modulus previous) (7 * modulus.length)).map
      Configuration.outputBits).map Binary.value =
      (Foundation.Probability.uniform (Fin (2 ^ modulus.length))).map Fin.val := by
  rw [candidateScan_output modulus previous h, PMF.map_comp]
  have hUniform := uniform_map_equiv (Binary.bitsEquiv modulus.length)
  rw [← hUniform, PMF.map_comp]
  rfl

/-- Candidate generation after the validator's real tape restoration has
exactly the same bit law. Redundant blanks are a proof relation only. -/
theorem validatedScan_output (modulus : List Bool) :
    (evalConfigWithin program (validatedTrialStart modulus) (7 * modulus.length)).map
      Configuration.outputBits =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map List.ofFn := by
  have h := evalConfigWithin_map_eq_of_equivalent program
    (validatedTrialStart modulus) (trialStart modulus [])
    (validatedTrialStart_equivalent modulus) (7 * modulus.length)
    Configuration.outputBits (fun _ _ h => h.outputBits)
  rw [h]
  exact candidateScan_output modulus [] (by simp)

/-- Validation, charged head restoration, and actual fair-bit generation
compose without substituting a mathematical sampler instruction. -/
theorem validateAndScan_output (leading : List Bool) :
    let modulus := leading ++ [true]
    (evalConfigWithin program (validationStart modulus) (11 * modulus.length + 5)).map
      Configuration.outputBits =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map List.ofFn := by
  dsimp only
  have hBudget : 11 * (leading ++ [true]).length + 5 =
      (4 * (leading ++ [true]).length + 5) + 7 * (leading ++ [true]).length := by omega
  rw [hBudget, evalConfigWithin_add, eval_validateBody, PMF.pure_bind]
  exact validatedScan_output _

theorem empty_haltsWithin : HaltsWithin program [] 2 := by
  rw [haltsWithin_iff_reachableStates]
  decide

/-- A complete trial counts all candidate steps and both charged rewinds.
Accepted branches are already halted during the remaining inspections. -/
theorem eval_trial (modulus previous : List Bool)
    (hPrevious : previous.length ≤ modulus.length) :
    evalConfigWithin program (trialStart modulus previous) (10 * modulus.length + 7) =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map (trialResult modulus) := by
  have hBudget : 10 * modulus.length + 7 = 7 * modulus.length + (3 * modulus.length + 7) := by omega
  rw [hBudget, evalConfigWithin_add, eval_candidateScan, PMF.bind_map]
  simp only [Function.comp_def, candidateFinish_tail modulus previous _ hPrevious]
  exact PMF.bind_pure_comp _ _

theorem trialResult_halted (modulus : List Bool) (bits : Fin modulus.length → Bool) :
    (trialResult modulus bits).halted =
      decide (Binary.value (List.ofFn bits) < Binary.value modulus) := by
  by_cases h : Binary.value (List.ofFn bits) < Binary.value modulus <;>
    simp [trialResult, accepted, retryStart, h]

theorem trialResult_output (modulus : List Bool) (bits : Fin modulus.length → Bool) :
    (trialResult modulus bits).outputBits = List.ofFn bits := by
  by_cases h : Binary.value (List.ofFn bits) < Binary.value modulus
  · simp [trialResult, accepted, h, Configuration.outputBits, Tape.bits, -List.map_ofFn]
  · have hCells := rewindBitstringFinish_input_equivalent (List.ofFn bits) {}
    have hTape : (Tape.ofBits (List.ofFn bits)).bits = List.ofFn bits := by
      cases hList : List.ofFn bits <;> simp [Tape.ofBits, Tape.bits]
    simp only [trialResult, h, ↓reduceIte, retryStart, Configuration.outputBits]
    exact hCells.bits.trans hTape

theorem trialResult_retry_equivalent (modulus : List Bool) (bits : Fin modulus.length → Bool)
    (h : ¬ Binary.value (List.ofFn bits) < Binary.value modulus) :
    (trialResult modulus bits).Equivalent (trialStart modulus (List.ofFn bits)) := by
  simp only [trialResult, h, ↓reduceIte]
  exact ⟨rfl, rfl, rewindBitstringFinish_input_equivalent modulus {},
    rewindBitstringFinish_input_equivalent (List.ofFn bits) {}⟩

namespace Saved

def initial (before : List (Option Bool)) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := none :: before } }

def validationStart (before : List (Option Bool)) (bits : List Bool) : Configuration :=
  { pc := 7, inputTape := { Tape.ofBits bits with left := none :: before } }

theorem eval_guard_false (before : List (Option Bool)) (rest : List Bool) :
    evalConfigWithin program (initial before (false::rest)) 1 =
      PMF.pure (validationStart before (false::rest)) := by
  simp [evalConfigWithin, stepPMF, next, program, initial, validationStart,
    Tape.ofBits, Instruction.next, Configuration.tape, PMF.pure_bind]

theorem eval_guard_true (before : List (Option Bool)) (bit : Bool) (rest : List Bool) :
    evalConfigWithin program (initial before (true::bit::rest)) 5 =
      PMF.pure (validationStart before (true::bit::rest)) := by
  cases bit <;> simp [evalConfigWithin, stepPMF, next, program, initial, validationStart,
    Tape.ofBits, Tape.moveRight, Tape.moveLeft, Instruction.next, Configuration.tape,
    Configuration.advance, Configuration.updateTape, PMF.pure_bind]

private def validationRewindState (before : List (Option Bool)) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 13, inputTape := { left := left.map some ++ none :: before, current := current, right := right } }

private def validationRewindFinish (before : List (Option Bool)) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 17, inputTape := ({ left := before, right := left.reverse.map some ++ current::right } : Tape).moveRight }

private theorem eval_validation_rewind (before : List (Option Bool)) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    evalConfigWithin program (validationRewindState before left current right) (2*left.length+4) =
      PMF.pure (validationRewindFinish before left current right) := by
  induction left generalizing current right with
  | nil =>
    simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
      validationRewindState, validationRewindFinish, Instruction.next, Configuration.tape,
      Configuration.advance, Configuration.updateTape, Tape.moveLeft, Tape.moveRight, PMF.pure_bind]
  | cons bit rest ih =>
    have budget : 2*(bit::rest).length+4 = 2+(2*rest.length+4) := by simp; omega
    have pair : evalConfigWithin program (validationRewindState before (bit::rest) current right) 2 =
        PMF.pure (validationRewindState before rest (some bit) (current::right)) := by
      cases bit <;> simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
        validationRewindState, Instruction.next, Configuration.tape, Configuration.advance,
        Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]
    rw [budget, evalConfigWithin_add, pair, PMF.pure_bind, ih]
    simp [validationRewindFinish, List.reverse_cons, List.map_append, List.append_assoc]

def validatedTrialStart (before : List (Option Bool)) (bits : List Bool) : Configuration :=
  { pc := 17, inputTape := ({ left := before, right := bits.map some ++ [none] } : Tape).moveRight }

/-- Validation and its native rewind preserve the caller's saved counter.
The four-per-bit preparation cost is unchanged. -/
theorem eval_validateBody (before : List (Option Bool)) (leading : List Bool) :
    let bits := leading ++ [true]
    evalConfigWithin program (validationStart before bits) (4*bits.length+5) =
      PMF.pure (validatedTrialStart before bits) := by
  dsimp only
  have start (bits : List Bool) (steps : Nat) :
      evalConfigWithin program (validationStart before bits) (steps+1) =
        evalConfigWithin program (validationState false (none::before) bits) (steps+1) := by
    rw [evalConfigWithin_succ_head, evalConfigWithin_succ_head]
    congr 1
  rw [show 4*(leading++[true]).length+5 =
    (2*(leading++[true]).length+1)+(2*(leading++[true]).length+4) by omega,
    evalConfigWithin_add, start, eval_validation, PMF.pure_bind]
  simp only [lastSeen_one, ↓reduceIte]
  simpa [validationRewindState, validationRewindFinish, validatedTrialStart] using
    eval_validation_rewind before (leading++[true]).reverse none []

/-- The same retry loop with a caller prefix protected by a real blank.
The saved width counter lies in this prefix and is not part of the modulus. -/
def trialStart (before : List (Option Bool)) (modulus previous : List Bool) : Configuration :=
  { pc := 17
    inputTape := { Tape.ofBits modulus with left := none :: before }
    outputTape := Tape.ofBits previous }

theorem validatedTrialStart_equivalent (before : List (Option Bool)) (bits : List Bool) :
    (validatedTrialStart before bits).Equivalent (trialStart before bits []) :=
  ⟨rfl, rfl, rewindBitstring_saved_input_equivalent bits before 0, Tape.Equivalent.refl _⟩

/-- The q=1 fast path still produces its unique scalar and retains the
saved width counter on the input tape. -/
theorem one_eval (before : List (Option Bool)) :
    evalConfigWithin program (initial before [true]) 5 =
      PMF.pure ({ pc := 4, halted := true, inputTape := { left := some true :: none :: before }, outputTape := { current := some false } } : Configuration) := by
  simp [evalConfigWithin, stepPMF, next, program, initial, Instruction.next,
    Configuration.advance, Configuration.updateTape, Configuration.tape,
    Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private def rewindState (before : List (Option Bool)) (left : List (Bool × Bool))
    (ic oc : Option Bool) (ir orr : List (Option Bool)) : Configuration :=
  { pc := 41
    inputTape := { left := (left.map Prod.fst).map some ++ none :: before, current := ic, right := ir }
    outputTape := { left := (left.map Prod.snd).map some, current := oc, right := orr } }

private def rewindFinish (before : List (Option Bool)) (left : List (Bool × Bool))
    (ic oc : Option Bool) (ir orr : List (Option Bool)) : Configuration :=
  { pc := 17
    inputTape := ({ left := before, right := (left.map Prod.fst).reverse.map some ++ ic :: ir } : Tape).moveRight
    outputTape := ({ right := (left.map Prod.snd).reverse.map some ++ oc :: orr } : Tape).moveRight }

private theorem eval_rewind (before : List (Option Bool)) (left : List (Bool × Bool))
    (ic oc : Option Bool) (ir orr : List (Option Bool)) :
    evalConfigWithin program (rewindState before left ic oc ir orr) (3*left.length+6) =
      PMF.pure (rewindFinish before left ic oc ir orr) := by
  induction left generalizing ic oc ir orr with
  | nil =>
    simp [evalConfigWithin, stepPMF, next, program, retryBody, offset, rewindState,
      rewindFinish, Instruction.next, Configuration.tape, Configuration.advance,
      Configuration.updateTape, Tape.moveLeft, Tape.moveRight, PMF.pure_bind]
  | cons pair rest ih =>
    rcases pair with ⟨inputBit, outputBit⟩
    have budget : 3*((inputBit, outputBit)::rest).length+6 = 3+(3*rest.length+6) := by simp; omega
    have first : evalConfigWithin program
        (rewindState before ((inputBit, outputBit)::rest) ic oc ir orr) 3 =
        PMF.pure (rewindState before rest (some inputBit) (some outputBit) (ic::ir) (oc::orr)) := by
      cases inputBit <;> simp [evalConfigWithin, stepPMF, next, program, retryBody, offset,
        rewindState, Instruction.next, Configuration.tape, Configuration.advance,
        Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]
    rw [budget, evalConfigWithin_add, first, PMF.pure_bind, ih]
    simp [rewindFinish, List.reverse_cons, List.map_append, List.append_assoc]

private def accepted (before : List (Option Bool)) (modulus candidate : List Bool) : Configuration :=
  { pc := 48
    halted := true
    inputTape := { left := modulus.reverse.map some ++ none :: before }
    outputTape := { left := candidate.reverse.map some } }

private def retryStart (before : List (Option Bool)) (modulus candidate : List Bool) : Configuration :=
  { pc := 17
    inputTape := ({ left := before, right := modulus.map some ++ [none] } : Tape).moveRight
    outputTape := ({ right := candidate.map some ++ [none] } : Tape).moveRight }

def trialResult (before : List (Option Bool)) (modulus : List Bool) (bits : Fin modulus.length → Bool) : Configuration :=
  if Binary.value (List.ofFn bits) < Binary.value modulus then
    accepted before modulus (List.ofFn bits)
  else retryStart before modulus (List.ofFn bits)

private def endState (before : List (Option Bool)) (prior : Ordering) (modulus candidate : List Bool) : Configuration :=
  { pc := scanAddress prior
    inputTape := { left := modulus.reverse.map some ++ none :: before }
    outputTape := { left := candidate.reverse.map some } }

private theorem eval_tail (before : List (Option Bool)) (prior : Ordering) (modulus candidate : List Bool)
    (hLength : candidate.length = modulus.length) :
    evalConfigWithin program (endState before prior modulus candidate) (3*modulus.length+7) =
      PMF.pure (if prior = .lt then accepted before modulus candidate else retryStart before modulus candidate) := by
  have hFirst : (modulus.zip candidate).map Prod.fst = modulus := List.map_fst_zip (by omega)
  have hSecond : (modulus.zip candidate).map Prod.snd = candidate := List.map_snd_zip (by omega)
  have rewind : evalConfigWithin program
      ({ pc := 41, inputTape := { left := modulus.reverse.map some ++ none :: before },
         outputTape := { left := candidate.reverse.map some } } : Configuration)
      (3*modulus.length+6) = PMF.pure (retryStart before modulus candidate) := by
    simpa [rewindState, rewindFinish, retryStart, List.map_reverse, hFirst, hSecond,
      List.length_zip, hLength] using eval_rewind before (modulus.zip candidate).reverse none none [] []
  cases prior with
  | eq =>
    have step : evalConfigWithin program (endState before .eq modulus candidate) 1 =
        PMF.pure ({ pc := 41, inputTape := { left := modulus.reverse.map some ++ none :: before },
                    outputTape := { left := candidate.reverse.map some } } : Configuration) := by
      simp [evalConfigWithin, stepPMF, next, program, retryBody, offset, endState,
        scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
    rw [show 3*modulus.length+7 = 1+(3*modulus.length+6) by omega,
      evalConfigWithin_add, step, PMF.pure_bind, rewind]
    simp
  | lt =>
    have step : evalConfigWithin program (endState before .lt modulus candidate) 2 =
        PMF.pure (accepted before modulus candidate) := by
      simp [evalConfigWithin, stepPMF, next, program, retryBody, offset, endState,
        accepted, scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
    rw [show 3*modulus.length+7 = 2+(3*modulus.length+5) by omega,
      evalConfigWithin_add, step, PMF.pure_bind, eval_halted _ _ rfl]
    simp
  | gt =>
    have step : evalConfigWithin program (endState before .gt modulus candidate) 1 =
        PMF.pure ({ pc := 41, inputTape := { left := modulus.reverse.map some ++ none :: before },
                    outputTape := { left := candidate.reverse.map some } } : Configuration) := by
      simp [evalConfigWithin, stepPMF, next, program, retryBody, offset, endState,
        scanAddress, Instruction.next, Configuration.tape, PMF.pure_bind]
    rw [show 3*modulus.length+7 = 1+(3*modulus.length+6) by omega,
      evalConfigWithin_add, step, PMF.pure_bind, rewind]
    simp

/-- One complete candidate trial, including acceptance or actual head
restoration, has exactly the original finite candidate law. -/
theorem eval_trial (before : List (Option Bool)) (modulus previous : List Bool)
    (hPrevious : previous.length ≤ modulus.length) :
    evalConfigWithin program (trialStart before modulus previous) (10*modulus.length+7) =
      (Foundation.Probability.uniform (Fin modulus.length → Bool)).map (trialResult before modulus) := by
  have start : trialStart before modulus previous = scanState .eq (none::before) modulus [] (previous.map some) := by
    cases previous <;> rfl
  have oldEmpty : (previous.map some).drop modulus.length = [] := by
    rw [List.drop_eq_nil_iff]
    simpa using hPrevious
  rw [show 10*modulus.length+7 = 7*modulus.length+(3*modulus.length+7) by omega,
    start, evalConfigWithin_add, eval_scan, PMF.bind_map]
  simp only [Function.comp_def, oldEmpty, List.append_nil]
  have tail (bits : Fin modulus.length → Bool) :
      evalConfigWithin program
        (scanState (BinaryComparison.compare .eq ((List.ofFn bits).zip modulus))
          (modulus.reverse.map some ++ none::before) [] ((List.ofFn bits).reverse.map some) [])
        (3*modulus.length+7) = PMF.pure (trialResult before modulus bits) := by
    change evalConfigWithin program
      (endState before (BinaryComparison.compare .eq ((List.ofFn bits).zip modulus)) modulus (List.ofFn bits)) _ = _
    rw [eval_tail _ _ _ _ (by simp)]
    have first := List.map_fst_zip (l₁ := List.ofFn bits) (l₂ := modulus) (by simp)
    have second := List.map_snd_zip (l₁ := List.ofFn bits) (l₂ := modulus) (by simp)
    simp only [BinaryComparison.compare_values, first, second, trialResult]
    split_ifs <;> simp_all
  simp only [tail]
  exact PMF.bind_pure_comp _ _

theorem trialResult_halted (before : List (Option Bool)) (modulus : List Bool) (bits : Fin modulus.length → Bool) :
    (trialResult before modulus bits).halted =
      (if Binary.value (List.ofFn bits) < Binary.value modulus then true else false) := by
  unfold trialResult
  split_ifs <;> simp [accepted, retryStart]

theorem trialResult_output (before : List (Option Bool)) (modulus : List Bool) (bits : Fin modulus.length → Bool) :
    (trialResult before modulus bits).outputBits = List.ofFn bits := by
  unfold trialResult
  split_ifs
  · simp [accepted, Configuration.outputBits, Tape.bits, -List.map_ofFn]
  · have bitsEq : (Tape.ofBits (List.ofFn bits)).bits = List.ofFn bits := by
      cases hList : List.ofFn bits <;> simp [Tape.ofBits, Tape.bits]
    exact (rewindBitstringFinish_input_equivalent (List.ofFn bits) {}).bits.trans bitsEq

theorem trialResult_retry_equivalent (before : List (Option Bool)) (modulus : List Bool)
    (bits : Fin modulus.length → Bool) (h : ¬ Binary.value (List.ofFn bits) < Binary.value modulus) :
    (trialResult before modulus bits).Equivalent (trialStart before modulus (List.ofFn bits)) := by
  simp only [trialResult, h, ↓reduceIte]
  exact ⟨rfl, rfl, rewindBitstring_saved_input_equivalent modulus before 0,
    rewindBitstringFinish_input_equivalent (List.ofFn bits) {}⟩

theorem trialResult_accepted_input (before : List (Option Bool)) (modulus : List Bool)
    (bits : Fin modulus.length → Bool) (h : Binary.value (List.ofFn bits) < Binary.value modulus) :
    (trialResult before modulus bits).inputTape = { left := modulus.reverse.map some ++ none::before } := by
  simp only [trialResult, h, ↓reduceIte, accepted]

theorem trialResult_accepted_output (before : List (Option Bool)) (modulus : List Bool)
    (bits : Fin modulus.length → Bool) (h : Binary.value (List.ofFn bits) < Binary.value modulus) :
    (trialResult before modulus bits).outputTape = { left := (List.ofFn bits).reverse.map some } := by
  simp only [trialResult, h, ↓reduceIte, accepted]

end Saved

end Machine.RejectionSampling
