import Foundation.Crypto.Semantics.Machine.BinarySubtraction
import Foundation.Crypto.Semantics.Machine.BitstringRewind

set_option maxRecDepth 4096

namespace Machine.BinaryDoubleReduction

/-- One finite bit-level program for doubling a residue and adding one input
bit, followed by one conditional subtraction of the modulus. The input is a
header bit followed by interleaved equal-width residue/modulus bits. The
subtraction's borrow is finite control, and the underflow path restores both
physical heads before copying the original shifted operand. -/
def program : Program :=
  [
   .branch .input 107 1 3,
   .moveRight .input,
   .jump 10,
   .moveRight .input,
   .jump 58,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 106 11 14,
   .moveRight .input,
   .branch .input 107 16 20,
   .halt,
   .moveRight .input,
   .branch .input 107 24 28,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 34,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 58,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 82,
   .halt,
   .halt,
   .branch .input 109 35 38,
   .moveRight .input,
   .branch .input 107 40 44,
   .halt,
   .moveRight .input,
   .branch .input 107 48 52,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 34,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 34,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 82,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 82,
   .halt,
   .halt,
   .branch .input 106 59 62,
   .moveRight .input,
   .branch .input 107 64 68,
   .halt,
   .moveRight .input,
   .branch .input 107 72 76,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 58,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 58,
   .halt,
   .halt,
   .branch .input 109 83 86,
   .moveRight .input,
   .branch .input 107 88 92,
   .halt,
   .moveRight .input,
   .branch .input 107 96 100,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 34,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 58,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 82,
   .halt,
   .halt,
   .halt,
   .erase .output,
   .halt,
   .moveLeft .input,
   .moveLeft .input,
   .moveLeft .output,
   .branch .input 113 109 109,
   .moveRight .input,
   .moveRight .output,
   .branch .input 107 116 120,
   .moveRight .input,
   .jump 124,
   .halt,
   .halt,
   .moveRight .input,
   .jump 140,
   .halt,
   .halt,
   .branch .input 156 125 128,
   .moveRight .input,
   .branch .input 107 130 130,
   .halt,
   .moveRight .input,
   .branch .input 107 134 134,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 124,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 140,
   .halt,
   .halt,
   .branch .input 156 141 144,
   .moveRight .input,
   .branch .input 107 146 146,
   .halt,
   .moveRight .input,
   .branch .input 107 150 150,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 124,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 140,
   .halt,
   .halt,
   .halt]

private def address (previous borrow : Bool) : Nat :=
  10 + 24 * (2 * previous.toNat + borrow.toNat)

private def state (previous borrow : Bool) (before : List (Option Bool))
    (bits : List Bool) (written : List (Option Bool)) : Configuration :=
  { pc := address previous borrow,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { left := written } }

private theorem eval_pair (previous borrow : Bool) (before written : List (Option Bool))
    (first second : Bool) (rest : List Bool) :
    evalConfigWithin program (state previous borrow before (first :: second :: rest) written) 7 =
      PMF.pure (state first (BinarySubtraction.nextBorrow borrow previous second)
        (some second :: some first :: before) rest
        (some (BinarySubtraction.digit borrow previous second) :: written)) := by
  cases previous <;> cases borrow <;> cases first <;> cases second <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address,
      BinarySubtraction.digit, BinarySubtraction.nextBorrow,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private def shiftedPairs : Bool → List (Bool × Bool) → List (Bool × Bool)
  | _, [] => []
  | previous, pair :: rest => (previous, pair.2) :: shiftedPairs pair.1 rest

private def lastBit : Bool → List (Bool × Bool) → Bool
  | previous, [] => previous
  | _, pair :: rest => lastBit pair.1 rest

/-- A complete first pass executes the subtract-and-shift circuit with its
finite-control borrow. The conditional-copy continuation has not yet run. -/
private theorem eval_pairs_context (pairs : List (Bool × Bool)) (previous borrow : Bool)
    (before written : List (Option Bool)) (following : List Bool) :
    evalConfigWithin program (state previous borrow before
      (BinaryComparison.interleave pairs ++ following) written) (7 * pairs.length) =
      PMF.pure (state (lastBit previous pairs)
        (BinarySubtraction.borrowOut borrow (shiftedPairs previous pairs))
        ((BinaryComparison.interleave pairs).reverse.map some ++ before) following
        ((BinarySubtraction.differenceBits borrow (shiftedPairs previous pairs)).reverse.map some ++ written)) := by
  induction pairs generalizing previous borrow before written with
  | nil => simp [evalConfigWithin, lastBit, shiftedPairs, BinarySubtraction.borrowOut,
      BinarySubtraction.differenceBits, BinarySubtraction.lowerBits, BinaryComparison.interleave]
  | cons pair rest ih =>
      have hBudget : 7 * (pair :: rest).length = 7 + 7 * rest.length := by simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [BinaryComparison.interleave, List.cons_append, eval_pair, PMF.pure_bind, ih,
        shiftedPairs, lastBit, BinarySubtraction.borrowOut, BinarySubtraction.differenceBits,
        BinarySubtraction.lowerBits]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem eval_pairs (pairs : List (Bool × Bool)) (previous borrow : Bool)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state previous borrow before
      (BinaryComparison.interleave pairs) written) (7 * pairs.length) =
      PMF.pure (state (lastBit previous pairs)
        (BinarySubtraction.borrowOut borrow (shiftedPairs previous pairs))
        ((BinaryComparison.interleave pairs).reverse.map some ++ before) []
        ((BinarySubtraction.differenceBits borrow (shiftedPairs previous pairs)).reverse.map some ++ written)) := by
  simpa using eval_pairs_context pairs previous borrow before written []

private def copyAddress (previous : Bool) : Nat := if previous then 140 else 124

private def rewindState (header : Bool) (remaining : List ((Bool × Bool) × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    Configuration :=
  { pc := 109,
    inputTape := {
      left := remaining.flatMap (fun pair => [some pair.1.2, some pair.1.1]) ++ [some header],
      current := currentInput, right := afterInput },
    outputTape := {
      left := remaining.map (fun pair => some pair.2),
      current := currentOutput, right := afterOutput } }

private def rewindFinish (header : Bool) (remaining : List ((Bool × Bool) × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    Configuration :=
  { pc := copyAddress header,
    inputTape := (({ right := some header ::
      remaining.reverse.flatMap (fun pair => [some pair.1.1, some pair.1.2]) ++
        currentInput :: afterInput } : Tape).moveRight).moveRight,
    outputTape := ({ right := remaining.reverse.map (fun pair => some pair.2) ++
      currentOutput :: afterOutput } : Tape).moveRight }

private theorem eval_rewind_bit (header first second output : Bool)
    (remaining : List ((Bool × Bool) × Bool)) (currentInput currentOutput : Option Bool)
    (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program
      (rewindState header (((first, second), output) :: remaining)
        currentInput currentOutput afterInput afterOutput) 4 =
      PMF.pure (rewindState header remaining (some first) (some output)
        (some second :: currentInput :: afterInput) (currentOutput :: afterOutput)) := by
  cases first <;>
    simp [evalConfigWithin, stepPMF, next, program, rewindState,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]

private theorem eval_rewind_end (header : Bool) (currentInput currentOutput : Option Bool)
    (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program (rewindState header [] currentInput currentOutput afterInput afterOutput) 9 =
      PMF.pure (rewindFinish header [] currentInput currentOutput afterInput afterOutput) := by
  cases header <;>
    simp [evalConfigWithin, stepPMF, next, program, rewindState, rewindFinish, copyAddress,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, Tape.moveRight, PMF.pure_bind]

/-- Both heads are restored by charged instructions, while every written
cell of the input and candidate tapes is preserved. -/
private theorem eval_rewind (header : Bool) (remaining : List ((Bool × Bool) × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program (rewindState header remaining currentInput currentOutput afterInput afterOutput)
      (4 * remaining.length + 9) =
      PMF.pure (rewindFinish header remaining currentInput currentOutput afterInput afterOutput) := by
  induction remaining generalizing currentInput currentOutput afterInput afterOutput with
  | nil => simpa using eval_rewind_end header currentInput currentOutput afterInput afterOutput
  | cons pair rest ih =>
      rcases pair with ⟨⟨first, second⟩, output⟩
      have hBudget : 4 * (((first, second), output) :: rest).length + 9 =
          4 + (4 * rest.length + 9) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_rewind_bit, PMF.pure_bind, ih]
      simp [rewindFinish, List.reverse_cons, List.flatMap_append, List.map_append,
        List.append_assoc]

private def copyState (previous : Bool) (before : List (Option Bool)) (bits : List Bool)
    (written : List (Option Bool)) (old : List Bool) : Configuration :=
  { pc := copyAddress previous,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { Tape.ofBits old with left := written } }

private def copyFinish (before written : List (Option Bool)) (old : List Bool) : Configuration :=
  { pc := 156, inputTape := { left := before },
    outputTape := { Tape.ofBits old with left := written }, halted := true }

set_option maxHeartbeats 800000 in
private theorem eval_copy_pair (previous first second : Bool) (before written : List (Option Bool))
    (rest old : List Bool) :
    evalConfigWithin program (copyState previous before (first :: second :: rest) written old) 7 =
      PMF.pure (copyState first (some second :: some first :: before) rest
        (some previous :: written) old.tail) := by
  cases old with
  | nil =>
      cases previous <;> cases first <;> cases second <;> cases rest <;>
      simp [evalConfigWithin, stepPMF, next, program, copyState, copyAddress,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]
  | cons oldBit oldRest =>
      cases oldRest <;> cases previous <;> cases first <;> cases second <;> cases rest <;>
      simp [evalConfigWithin, stepPMF, next, program, copyState, copyAddress,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_copy_end (previous : Bool) (before written : List (Option Bool))
    (old : List Bool) :
    evalConfigWithin program (copyState previous before [] written old) 2 =
      PMF.pure (copyFinish before written old) := by
  cases previous <;>
    simp [evalConfigWithin, stepPMF, next, program, copyState, copyAddress, copyFinish,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

set_option maxHeartbeats 800000 in
private theorem eval_copy_pairs (previous : Bool) (pairs : List (Bool × Bool))
    (before written : List (Option Bool)) (old : List Bool) :
    evalConfigWithin program (copyState previous before (BinaryComparison.interleave pairs) written old)
      (7 * pairs.length + 2) =
      PMF.pure (copyFinish ((BinaryComparison.interleave pairs).reverse.map some ++ before)
        (((shiftedPairs previous pairs).map Prod.fst).reverse.map some ++ written)
        (old.drop pairs.length)) := by
  induction pairs generalizing previous before written old with
  | nil => simpa [BinaryComparison.interleave, shiftedPairs] using eval_copy_end previous before written old
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have hBudget : 7 * ((first, second) :: rest).length + 2 = 7 + (7 * rest.length + 2) := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [BinaryComparison.interleave, eval_copy_pair, PMF.pure_bind, ih,
        shiftedPairs, List.map_cons, List.length_cons]
      simp [List.reverse_cons, List.map_append, List.append_assoc, List.drop_tail]

private theorem shiftedPairs_length (previous : Bool) (pairs : List (Bool × Bool)) :
    (shiftedPairs previous pairs).length = pairs.length := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair rest ih => simp [shiftedPairs, ih]

private theorem shiftedPairs_snd (previous : Bool) (pairs : List (Bool × Bool)) :
    (shiftedPairs previous pairs).map Prod.snd = pairs.map Prod.snd := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair rest ih => simp [shiftedPairs, ih]

private theorem shiftedPairs_value (previous : Bool) (pairs : List (Bool × Bool)) :
    Binary.value ((shiftedPairs previous pairs).map Prod.fst) +
      2 ^ pairs.length * (lastBit previous pairs).toNat =
      2 * Binary.value (pairs.map Prod.fst) + previous.toNat := by
  induction pairs generalizing previous with
  | nil => simp [shiftedPairs, lastBit, Binary.value]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have h := congrArg (fun x : Nat => 2 * x) (ih first)
      simp only [shiftedPairs, List.map_cons, Binary.value, lastBit, List.length_cons, pow_succ]
      ring_nf at h ⊢
      omega

private theorem interleave_flatMap (pairs : List (Bool × Bool)) :
    BinaryComparison.interleave pairs = pairs.flatMap (fun pair => [pair.1, pair.2]) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [BinaryComparison.interleave, ih]

private theorem zip_input_cells (pairs : List (Bool × Bool)) (old : List Bool)
    (hLength : old.length = pairs.length) :
    (pairs.zip old).flatMap (fun pair => [some pair.1.1, some pair.1.2]) =
      (BinaryComparison.interleave pairs).map some := by
  have hFirst := List.map_fst_zip (l₁ := pairs) (l₂ := old) (by omega)
  have h := congrArg (fun xs : List (Bool × Bool) =>
    xs.flatMap (fun pair => [some pair.1, some pair.2])) hFirst
  simpa only [List.flatMap_map, interleave_flatMap, List.map_flatMap, List.map_cons,
    List.map_nil] using h

private theorem zip_output_cells (pairs : List (Bool × Bool)) (old : List Bool)
    (hLength : old.length = pairs.length) :
    (pairs.zip old).map (fun pair => some pair.2) = old.map some := by
  have h := congrArg (List.map some)
    (List.map_snd_zip (l₁ := pairs) (l₂ := old) (by omega))
  simpa only [List.map_map, Function.comp_def] using h

private theorem rewindState_eq (header : Bool) (pairs : List (Bool × Bool)) (old : List Bool)
    (hLength : old.length = pairs.length) :
    rewindState header (pairs.zip old).reverse none none [] [] =
      { pc := 109,
        inputTape := { left := (BinaryComparison.interleave pairs).reverse.map some ++ [some header] },
        outputTape := { left := old.reverse.map some } } := by
  have hInput : (pairs.zip old).reverse.flatMap (fun pair => [some pair.1.2, some pair.1.1]) =
      (BinaryComparison.interleave pairs).reverse.map some := by
    rw [List.flatMap_reverse]
    simpa [Function.comp_def, ← List.map_reverse] using
      congrArg List.reverse (zip_input_cells pairs old hLength)
  simp [rewindState, hInput, List.map_reverse, zip_output_cells pairs old hLength]

private theorem rewindFinish_equivalent (header : Bool) (pairs : List (Bool × Bool))
    (old : List Bool) (hLength : old.length = pairs.length) :
    (rewindFinish header (pairs.zip old).reverse none none [] []).Equivalent
      (copyState header [some header] (BinaryComparison.interleave pairs) [] old) := by
  have hInput := zip_input_cells pairs old hLength
  have hOutput := zip_output_cells pairs old hLength
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have h := (rewindBitstringFinish_input_equivalent
      (header :: BinaryComparison.interleave pairs) {}).moveRight
    cases hBits : BinaryComparison.interleave pairs <;>
      simpa [rewindFinish, rewindBitstringFinish, copyState, hInput, Tape.ofBits,
        Tape.moveRight, hBits] using h
  · have h := rewindBitstringFinish_input_equivalent old {}
    cases old <;> simpa [rewindFinish, rewindBitstringFinish, copyState, hOutput, Tape.ofBits] using h

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_copy_output (header : Bool) (pairs : List (Bool × Bool)) (old : List Bool)
    (hLength : old.length = pairs.length) :
    (evalConfigWithin program (copyState header [some header]
      (BinaryComparison.interleave pairs) [] old) (7 * pairs.length + 2)).map
      (fun c => if c.halted then some c.outputBits else none) =
        PMF.pure (some ((shiftedPairs header pairs).map Prod.fst)) := by
  rw [eval_copy_pairs, PMF.pure_map]
  have hDrop : old.drop pairs.length = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp [copyFinish, hDrop, Configuration.outputBits, Tape.bits, Tape.ofBits]

private def acceptedFinish (header : Bool) (pairs : List (Bool × Bool)) (old : List Bool) :
    Configuration :=
  { pc := 106,
    inputTape := { left := (BinaryComparison.interleave pairs).reverse.map some ++ [some header] },
    outputTape := { left := old.reverse.map some }, halted := true }

private theorem eval_accept (previous header : Bool) (pairs : List (Bool × Bool)) (old : List Bool) :
    evalConfigWithin program (state previous false
      ((BinaryComparison.interleave pairs).reverse.map some ++ [some header]) []
      (old.reverse.map some)) 2 = PMF.pure (acceptedFinish header pairs old) := by
  cases previous <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, acceptedFinish,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_select_rewind (previous header : Bool) (pairs : List (Bool × Bool))
    (old : List Bool) (hLength : old.length = pairs.length) :
    evalConfigWithin program (state previous true
      ((BinaryComparison.interleave pairs).reverse.map some ++ [some header]) []
      (old.reverse.map some)) 1 =
      PMF.pure (rewindState header (pairs.zip old).reverse none none [] []) := by
  rw [rewindState_eq header pairs old hLength]
  cases previous <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

/-- Selection, charged rewind, and overwrite of the candidate all belong to
the original finite code. The returned code uses the same width as the input. -/
private theorem eval_tail (previous borrow header : Bool) (pairs : List (Bool × Bool))
    (old : List Bool) (hLength : old.length = pairs.length) :
    (evalConfigWithin program (state previous borrow
      ((BinaryComparison.interleave pairs).reverse.map some ++ [some header]) []
      (old.reverse.map some)) (11 * pairs.length + 12)).map
      (fun c => if c.halted then some c.outputBits else none) =
      PMF.pure (some (if borrow then (shiftedPairs header pairs).map Prod.fst else old)) := by
  cases borrow with
  | false =>
      have hBudget : 11 * pairs.length + 12 = 2 + (11 * pairs.length + 10) := by omega
      rw [hBudget, evalConfigWithin_add, eval_accept, PMF.pure_bind,
        eval_halted _ _ rfl, PMF.pure_map]
      simp [acceptedFinish, Configuration.outputBits, Tape.bits]
  | true =>
      have hBudget : 11 * pairs.length + 12 = 1 + ((4 * pairs.length + 9) + (7 * pairs.length + 2)) := by omega
      rw [hBudget, evalConfigWithin_add, eval_select_rewind previous header pairs old hLength,
        PMF.pure_bind, evalConfigWithin_add]
      have hRewind := eval_rewind header (pairs.zip old).reverse none none [] []
      have hCount : (pairs.zip old).reverse.length = pairs.length := by
        simp [List.length_zip, hLength]
      rw [hCount] at hRewind
      rw [hRewind, PMF.pure_bind]
      exact ((rewindFinish_equivalent header pairs old hLength).evalOutput program
        (7 * pairs.length + 2)).trans (eval_copy_output header pairs old hLength)

private theorem eval_header_context (header : Bool) (following : List Bool) :
    evalConfigWithin program (Configuration.initial
      (header :: following)) 3 =
      PMF.pure (state header false [some header] (following) []) := by
  cases header <;> cases hBits : following <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, Configuration.initial,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem eval_header (header : Bool) (pairs : List (Bool × Bool)) :
    evalConfigWithin program (Configuration.initial
      (header :: BinaryComparison.interleave pairs)) 3 =
      PMF.pure (state header false [some header] (BinaryComparison.interleave pairs) []) := by
  exact eval_header_context header (BinaryComparison.interleave pairs)

/-- The operational result of the conditional subtraction helper. Arithmetic
correctness is stated separately, to distinguish the code from its numeric
specification. -/
private theorem eval_interleave (header : Bool) (pairs : List (Bool × Bool)) :
    evalWithin program (header :: BinaryComparison.interleave pairs) (18 * pairs.length + 15) =
      PMF.pure (some
        (if BinarySubtraction.borrowOut false (shiftedPairs header pairs) then
          (shiftedPairs header pairs).map Prod.fst
        else BinarySubtraction.differenceBits false (shiftedPairs header pairs))) := by
  have hBudget : 18 * pairs.length + 15 = 3 + (7 * pairs.length + (11 * pairs.length + 12)) := by omega
  unfold evalWithin
  rw [hBudget, evalConfigWithin_add, eval_header, PMF.pure_bind,
    evalConfigWithin_add, eval_pairs, PMF.pure_bind]
  simp only [List.append_nil]
  exact eval_tail (lastBit header pairs)
    (BinarySubtraction.borrowOut false (shiftedPairs header pairs)) header pairs
    (BinarySubtraction.differenceBits false (shiftedPairs header pairs))
    (by simp [shiftedPairs_length])

private def reducedBits (header : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  if BinarySubtraction.borrowOut false (shiftedPairs header pairs) then
    (shiftedPairs header pairs).map Prod.fst
  else BinarySubtraction.differenceBits false (shiftedPairs header pairs)

private theorem reducedBits_length (header : Bool) (pairs : List (Bool × Bool)) :
    (reducedBits header pairs).length = pairs.length := by
  unfold reducedBits
  split <;> simp [shiftedPairs_length]

/-- Complete bit columns always produce a result of the same width, even
when the numeric preconditions of modular correctness do not hold. This
structural property supports native caller termination on malformed data. -/
theorem complete_output (header : Bool) (pairs : List (Bool × Bool)) :
    ∃ output : List Bool, output.length = pairs.length ∧
    evalWithin program (header :: BinaryComparison.interleave pairs) (18 * pairs.length + 15) =
      PMF.pure (some output) :=
  ⟨reducedBits header pairs, reducedBits_length header pairs, eval_interleave header pairs⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem reducedBits_value (header : Bool) (pairs : List (Bool × Bool))
    (hResidue : Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd))
    (hWidth : 2 * Binary.value (pairs.map Prod.fst) + header.toNat < 2 ^ pairs.length) :
    Binary.value (reducedBits header pairs) =
      (2 * Binary.value (pairs.map Prod.fst) + header.toNat) % Binary.value (pairs.map Prod.snd) := by
  have hShift := shiftedPairs_value header pairs
  have hLast : lastBit header pairs = false := by
    cases h : lastBit header pairs with
    | false => rfl
    | true =>
        simp only [h, Bool.toNat_true, Nat.mul_one] at hShift
        omega
  rw [hLast] at hShift
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hShift
  have hInvariant := BinarySubtraction.differenceBits_invariant false (shiftedPairs header pairs)
  simp only [shiftedPairs_snd, shiftedPairs_length, Bool.toNat_false, Nat.add_zero] at hInvariant
  have hDifference := Binary.value_lt (BinarySubtraction.differenceBits false (shiftedPairs header pairs))
  simp only [BinarySubtraction.differenceBits_length, shiftedPairs_length] at hDifference
  have hTwice : 2 * Binary.value (pairs.map Prod.fst) + header.toNat <
      2 * Binary.value (pairs.map Prod.snd) := by
    cases header <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  unfold reducedBits
  cases hBorrow : BinarySubtraction.borrowOut false (shiftedPairs header pairs) with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [hBorrow, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hInvariant
      have hGe : Binary.value (pairs.map Prod.snd) ≤
          2 * Binary.value (pairs.map Prod.fst) + header.toNat := by omega
      rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt (by omega)]
      omega
  | true =>
      simp only [↓reduceIte]
      simp only [hBorrow, Bool.toNat_true, Nat.mul_one] at hInvariant
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hShift

/-- Exact modular doubling and one-bit addition from actual tape transitions.
The residue must be below the positive modulus, and the equal input width
must have room for its double. These are numeric specifications of the input,
not unit-cost operations in the instruction set. -/
theorem eval_double_mod (header : Bool) (pairs : List (Bool × Bool))
    (hResidue : Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd))
    (hWidth : 2 * Binary.value (pairs.map Prod.fst) + header.toNat < 2 ^ pairs.length) :
    (evalWithin program (header :: BinaryComparison.interleave pairs) (18 * pairs.length + 15)).map
      (Option.map Binary.value) =
      PMF.pure (some ((2 * Binary.value (pairs.map Prod.fst) + header.toNat) %
        Binary.value (pairs.map Prod.snd))) := by
  rw [eval_interleave, PMF.pure_map]
  change PMF.pure (some (Binary.value (reducedBits header pairs))) = _
  rw [reducedBits_value header pairs hResidue hWidth]

/-- The exact output representation has the supplied width, not an
unbounded unary representation of the residue. -/
theorem eval_double_mod_encoded (header : Bool) (pairs : List (Bool × Bool))
    (hResidue : Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd))
    (hWidth : 2 * Binary.value (pairs.map Prod.fst) + header.toNat < 2 ^ pairs.length) :
    evalWithin program (header :: BinaryComparison.interleave pairs) (18 * pairs.length + 15) =
      PMF.pure (some (Binary.encode pairs.length
        ((2 * Binary.value (pairs.map Prod.fst) + header.toNat) % Binary.value (pairs.map Prod.snd)))) := by
  rw [eval_interleave]
  change PMF.pure (some (reducedBits header pairs)) = _
  have h := Binary.encode_value (reducedBits header pairs)
  rw [reducedBits_length, reducedBits_value header pairs hResidue hWidth] at h
  rw [h]

private def invalid (before written : List (Option Bool)) : Configuration :=
  { pc := 108, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_odd (previous borrow bit : Bool) (before written : List (Option Bool)) :
    evalConfigWithin program (state previous borrow before [bit] written) 5 =
      PMF.pure (invalid (some bit :: before) written) := by
  cases previous <;> cases borrow <;> cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem decompose_input (bits : List Bool) :
    ∃ pairs : List (Bool × Bool), ∃ trailing : Option Bool,
      bits = BinaryComparison.interleave pairs ++ trailing.toList := by
  match bits with
  | [] => exact ⟨[], none, rfl⟩
  | [bit] => exact ⟨[], some bit, rfl⟩
  | first :: second :: rest =>
      obtain ⟨pairs, trailing, h⟩ := decompose_input rest
      exact ⟨(first, second) :: pairs, trailing, by simp [BinaryComparison.interleave, h]⟩
termination_by bits.length

private theorem interleave_length (pairs : List (Bool × Bool)) :
    (BinaryComparison.interleave pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [BinaryComparison.interleave, ih]; omega

/-- Every raw input halts, including odd operand counts and the empty string.
The uniform linear bound covers the charged rewind and recopy path as well. -/
theorem haltsWithin (input : List Bool) :
    HaltsWithin program input (18 * (input.length + 1)) := by
  cases input with
  | nil =>
      have hEval : evalWithin program [] 3 = PMF.pure (some []) := by
        simp [evalWithin, evalConfigWithin, stepPMF, next, program, Configuration.initial,
          Instruction.next, Configuration.advance, Configuration.tape,
          Configuration.updateTape, Configuration.outputBits, Tape.ofBits, Tape.bits,
          Tape.write, PMF.pure_bind, PMF.pure_map]
      apply (haltsWithin_of_no_timeout_support program [] 3 (by simp [hEval])).mono
      norm_num
  | cons header rest =>
      obtain ⟨pairs, trailing, hRest⟩ := decompose_input rest
      subst rest
      cases trailing with
      | none =>
          simp only [Option.toList_none, List.append_nil]
          apply (haltsWithin_of_no_timeout_support program
            (header :: BinaryComparison.interleave pairs) (18 * pairs.length + 15)
            (by rw [eval_interleave]; simp)).mono
          simp [interleave_length]
          omega
      | some bit =>
          simp only [Option.toList_some]
          have hEval : evalWithin program (header :: (BinaryComparison.interleave pairs ++ [bit]))
              (7 * pairs.length + 8) = PMF.pure (some (invalid
                (some bit :: (BinaryComparison.interleave pairs).reverse.map some ++ [some header])
                ((BinarySubtraction.differenceBits false (shiftedPairs header pairs)).reverse.map some)).outputBits) := by
            have hBudget : 7 * pairs.length + 8 = 3 + (7 * pairs.length + 5) := by omega
            unfold evalWithin
            rw [hBudget, evalConfigWithin_add, eval_header_context, PMF.pure_bind,
              evalConfigWithin_add, eval_pairs_context, PMF.pure_bind, eval_odd, PMF.pure_map]
            simp [invalid]
          apply (haltsWithin_of_no_timeout_support program _ (7 * pairs.length + 8)
            (by rw [hEval]; simp)).mono
          simp [interleave_length]
          omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 18 * (length + 1),
    (PolynomiallyBounded.const 18).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.BinaryDoubleReduction
