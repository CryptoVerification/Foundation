import Foundation.Crypto.Semantics.Machine.BinaryModularAddition

namespace Machine.BinaryProductInitialization

/-- Native initialization of the modular-product work matrix. Each input
column contains operand/multiplier/modulus bits. The five output tracks are
accumulator, operand, modulus, multiplier, and an unprocessed-bit marker.
All copies and the two inserted bits are charged one-cell operations. -/
def program : Program :=
  [
   .branch .input 116 1 4,
   .moveRight .input,
   .branch .input 117 8 11,
   .halt,
   .moveRight .input,
   .branch .input 117 14 17,
   .halt,
   .halt,
   .moveRight .input,
   .branch .input 117 20 32,
   .halt,
   .moveRight .input,
   .branch .input 117 44 56,
   .halt,
   .moveRight .input,
   .branch .input 117 68 80,
   .halt,
   .moveRight .input,
   .branch .input 117 92 104,
   .halt,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .write .output false,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .write .output true,
   .moveRight .output,
   .moveRight .input,
   .jump 0,
   .halt,
   .erase .output,
   .halt]

/-- The five bit tracks are a tape layout, not machine registers storing
unbounded natural numbers. Every marker initially equals true. -/
def matrix : List BinaryModularAddition.Column → List Bool
  | [] => []
  | ((operand, multiplier), modulus) :: rest =>
      false :: operand :: modulus :: multiplier :: true :: matrix rest

private def state (before : List (Option Bool)) (bits : List Bool)
    (written : List (Option Bool)) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before },
    outputTape := { left := written } }

private def finish (before written : List (Option Bool)) : Configuration :=
  { pc := 116, inputTape := { left := before }, outputTape := { left := written }, halted := true }

set_option maxHeartbeats 500000 in
private theorem eval_column (operand multiplier modulus : Bool)
    (before written : List (Option Bool)) (rest : List Bool) :
    evalConfigWithin program (state before (operand :: multiplier :: modulus :: rest) written) 17 =
      PMF.pure (state (some modulus :: some multiplier :: some operand :: before) rest
        (some true :: some multiplier :: some modulus :: some operand :: some false :: written)) := by
  cases operand <;> cases multiplier <;> cases modulus <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_end (before written : List (Option Bool)) :
    evalConfigWithin program (state before [] written) 2 = PMF.pure (finish before written) := by
  simp [evalConfigWithin, stepPMF, next, program, state, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_columns (columns : List BinaryModularAddition.Column)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state before (BinaryModularAddition.interleave columns) written)
      (17 * columns.length + 2) =
      PMF.pure (finish ((BinaryModularAddition.interleave columns).reverse.map some ++ before)
        ((matrix columns).reverse.map some ++ written)) := by
  induction columns generalizing before written with
  | nil => simpa [BinaryModularAddition.interleave, matrix] using eval_end before written
  | cons column rest ih =>
      rcases column with ⟨⟨operand, multiplier⟩, modulus⟩
      have hBudget : 17 * (((operand, multiplier), modulus) :: rest).length + 2 =
          17 + (17 * rest.length + 2) := by simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [BinaryModularAddition.interleave, eval_column, PMF.pure_bind, ih, matrix]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem eval_interleave (columns : List BinaryModularAddition.Column) :
    evalWithin program (BinaryModularAddition.interleave columns) (17 * columns.length + 2) =
      PMF.pure (some (matrix columns)) := by
  have hInitial : Configuration.initial (BinaryModularAddition.interleave columns) =
      state [] (BinaryModularAddition.interleave columns) [] := by
    cases BinaryModularAddition.interleave columns <;> rfl
  unfold evalWithin
  rw [hInitial, eval_columns, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits]

theorem matrix_length (columns : List BinaryModularAddition.Column) :
    (matrix columns).length = 5 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [matrix, ih]; omega

private def invalid (before written : List (Option Bool)) : Configuration :=
  { pc := 118, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_short_one (operand : Bool) (before written : List (Option Bool)) :
    evalConfigWithin program (state before [operand] written) 5 =
      PMF.pure (invalid (some operand :: before) written) := by
  cases operand <;>
    simp [evalConfigWithin, stepPMF, next, program, state, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_short_two (operand multiplier : Bool) (before written : List (Option Bool)) :
    evalConfigWithin program (state before [operand, multiplier] written) 7 =
      PMF.pure (invalid (some multiplier :: some operand :: before) written) := by
  cases operand <;> cases multiplier <;>
    simp [evalConfigWithin, stepPMF, next, program, state, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_raw (bits : List Bool) (before written : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin program (state before bits written) (17 * (bits.length + 1)) = PMF.pure result := by
  match bits with
  | [] =>
      refine ⟨finish before written, rfl, ?_⟩
      change evalConfigWithin program (state before [] written) (2 + 15) = _
      rw [evalConfigWithin_add, eval_end, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [operand] =>
      refine ⟨invalid (some operand :: before) written, rfl, ?_⟩
      change evalConfigWithin program (state before [operand] written) (5 + 29) = _
      rw [evalConfigWithin_add, eval_short_one, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [operand, multiplier] =>
      refine ⟨invalid (some multiplier :: some operand :: before) written, rfl, ?_⟩
      change evalConfigWithin program (state before [operand, multiplier] written) (7 + 44) = _
      rw [evalConfigWithin_add, eval_short_two, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | operand :: multiplier :: modulus :: rest =>
      obtain ⟨result, hHalted, hEval⟩ := eval_raw rest
        (some modulus :: some multiplier :: some operand :: before)
        (some true :: some multiplier :: some modulus :: some operand :: some false :: written)
      refine ⟨result, hHalted, ?_⟩
      have hBudget : 17 * ((operand :: multiplier :: modulus :: rest).length + 1) =
          17 + (17 * (rest.length + 1) + 34) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_column, PMF.pure_bind,
        evalConfigWithin_add, hEval, PMF.pure_bind]
      exact eval_halted _ _ hHalted
termination_by bits.length

private theorem eval_raw_layout (bits : List Bool) (before written : List (Option Bool)) :
    ∃ (columns : List BinaryModularAddition.Column) (result : Configuration),
      columns.length ≤ bits.length ∧ result.halted = true ∧
      result.inputTape = { left := bits.reverse.map some ++ before } ∧
      result.outputTape = { left := (matrix columns).reverse.map some ++ written } ∧
      evalConfigWithin program (state before bits written) (17 * (bits.length + 1)) = PMF.pure result := by
  match bits with
  | [] =>
      refine ⟨[], finish before written, by simp, rfl, rfl, rfl, ?_⟩
      change evalConfigWithin program (state before [] written) (2 + 15) = _
      rw [evalConfigWithin_add, eval_end, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [operand] =>
      refine ⟨[], invalid (some operand :: before) written, by simp, rfl, rfl, rfl, ?_⟩
      change evalConfigWithin program (state before [operand] written) (5 + 29) = _
      rw [evalConfigWithin_add, eval_short_one, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [operand, multiplier] =>
      refine ⟨[], invalid (some multiplier :: some operand :: before) written, by simp, rfl, rfl, rfl, ?_⟩
      change evalConfigWithin program (state before [operand, multiplier] written) (7 + 44) = _
      rw [evalConfigWithin_add, eval_short_two, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | operand :: multiplier :: modulus :: rest =>
      obtain ⟨columns, result, hWidth, hHalted, hInput, hOutput, hEval⟩ := eval_raw_layout rest
        (some modulus :: some multiplier :: some operand :: before)
        (some true :: some multiplier :: some modulus :: some operand :: some false :: written)
      refine ⟨((operand, multiplier), modulus) :: columns, result, by simp; omega,
        hHalted, ?_, ?_, ?_⟩
      · simpa [List.reverse_cons, List.map_append, List.append_assoc] using hInput
      · simpa [matrix, List.reverse_cons, List.map_append, List.append_assoc] using hOutput
      · have hBudget : 17 * ((operand :: multiplier :: modulus :: rest).length + 1) =
            17 + (17 * (rest.length + 1) + 34) := by simp; omega
        rw [hBudget, evalConfigWithin_add, eval_column, PMF.pure_bind,
          evalConfigWithin_add, hEval, PMF.pure_bind]
        exact eval_halted _ _ hHalted
termination_by bits.length

/-- A truncated raw request still leaves a complete five-track matrix:
only its complete triples are copied. Both physical heads and every saved
prefix are described by the returned configuration, rather than reloaded
between initialization and the product loop. -/
theorem complete_matrix (input : List Bool) :
    ∃ (columns : List BinaryModularAddition.Column) (result : Configuration),
      columns.length ≤ input.length ∧ result.halted = true ∧
      result.inputTape = { left := input.reverse.map some } ∧
      result.outputTape = { left := (matrix columns).reverse.map some } ∧
      evalConfigWithin program (Configuration.initial input) (17 * (input.length + 1)) = PMF.pure result := by
  have initial : Configuration.initial input = state [] input [] := by cases input <;> rfl
  simpa only [initial, List.append_nil] using eval_raw_layout input [] []

/-- Initialization consumes the same complete triples with arbitrary caller
cells saved to the left of its input head. Incomplete trailing triples still
stop, and the saved cells remain behind the copied input. -/
theorem complete_matrix_context (input : List Bool)
    (before : List (Option Bool)) :
    ∃ (columns : List BinaryModularAddition.Column) (result : Configuration),
      columns.length ≤ input.length ∧ result.halted = true ∧
      result.inputTape = { left := input.reverse.map some ++ before } ∧
      result.outputTape = { left := (matrix columns).reverse.map some } ∧
      evalConfigWithin program
        ({ inputTape := { Tape.ofBits input with left := before } } : Configuration)
        (17 * (input.length + 1)) = PMF.pure result := by
  simpa only [state, List.append_nil] using eval_raw_layout input before []

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- All raw inputs halt, including either truncated-column length. The
certificate concerns this real initialization code, not the entire product
loop, which additionally needs arithmetic passes and marker consumption. -/
theorem haltsWithin (input : List Bool) : HaltsWithin program input (17 * (input.length + 1)) := by
  obtain ⟨result, hHalted, hEval⟩ := eval_raw input [] []
  have hInitial : Configuration.initial input = state [] input [] := by cases input <;> rfl
  intro finish run
  have hSupport := (mem_support_evalConfigWithin_iff program _ finish _).mpr run
  rw [hInitial, hEval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalted

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 17 * (length + 1),
    (PolynomiallyBounded.const 17).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- Caller-owned prefixes are already present. Initialization reads the
contiguous input suffix and writes only into the fresh output region. -/
def initializationStart (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits input with left := beforeInput }, outputTape := { left := beforeOutput } }

theorem eval_interleave_context (columns : List BinaryModularAddition.Column)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (initializationStart beforeInput beforeOutput (BinaryModularAddition.interleave columns))
      (17 * columns.length + 2) =
      PMF.pure {
        pc := 116,
        inputTape := { left := (BinaryModularAddition.interleave columns).reverse.map some ++ beforeInput },
        outputTape := { left := (matrix columns).reverse.map some ++ beforeOutput },
        halted := true } :=
  eval_columns columns beforeInput beforeOutput

/-- The same raw-input termination bound applies while caller data are
retained behind each head. Incomplete final columns also terminate. -/
theorem haltsFrom (input : List Bool) (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor program (initializationStart beforeInput beforeOutput input) result
      (17 * (input.length + 1))) : result.halted = true := by
  obtain ⟨finish, hHalted, hEval⟩ := eval_raw input beforeInput beforeOutput
  have hSupport := (mem_support_evalConfigWithin_iff program _ result _).mpr run
  change result ∈ (evalConfigWithin program (state beforeInput input beforeOutput)
    (17 * (input.length + 1))).support at hSupport
  rw [hEval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalted

end Machine.BinaryProductInitialization
