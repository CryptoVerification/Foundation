import Foundation.Crypto.Semantics.Machine.BinaryComparison

namespace Machine.BinarySubtraction

/-- Ripple-borrow subtraction on interleaved little-endian input. Borrow is one
finite-control bit; every output write and both head moves are actual steps. -/
def program : Program :=
  [.branch .input 40 1 4, .moveRight .input, .branch .input 44 6 16,
   .jump 44, .moveRight .input, .branch .input 44 11 6,
   .write .output false, .moveRight .input, .moveRight .output, .jump 0,
   .halt,
   .write .output true, .moveRight .input, .moveRight .output, .jump 0,
   .halt,
   .write .output true, .moveRight .input, .moveRight .output, .jump 20,
   .branch .input 40 21 24, .moveRight .input, .branch .input 44 26 31,
   .jump 44, .moveRight .input, .branch .input 44 6 26,
   .write .output true, .moveRight .input, .moveRight .output, .jump 20,
   .halt,
   .write .output false, .moveRight .input, .moveRight .output, .jump 20,
   .halt, .halt, .halt, .halt, .halt,
   .erase .output, .halt, .write .output true, .halt,
   .erase .output, .halt]

def digit (borrow first second : Bool) : Bool := borrow.xor (first.xor second)
def nextBorrow (borrow first second : Bool) : Bool :=
  (!first && second) || (borrow && (!first || second))

def lowerBits : Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | borrow, pair :: rest => digit borrow pair.1 pair.2 ::
      lowerBits (nextBorrow borrow pair.1 pair.2) rest

def borrowOut : Bool → List (Bool × Bool) → Bool
  | borrow, [] => borrow
  | borrow, pair :: rest => borrowOut (nextBorrow borrow pair.1 pair.2) rest

def differenceBits (borrow : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  lowerBits borrow pairs

private def state (borrow : Bool) (before : List (Option Bool)) (bits : List Bool)
    (written : List (Option Bool)) : Configuration :=
  { pc := if borrow then 20 else 0,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { left := written } }

private def finish (_borrow : Bool) (before written : List (Option Bool)) : Configuration :=
  { pc := 41,
    inputTape := { left := before },
    outputTape := { left := written },
    halted := true }

private theorem eval_pair (borrow : Bool) (before written : List (Option Bool))
    (first second : Bool) (rest : List Bool) :
    evalConfigWithin program (state borrow before (first :: second :: rest) written) 7 =
      PMF.pure (state (nextBorrow borrow first second)
        (some second :: some first :: before) rest (some (digit borrow first second) :: written)) := by
  cases borrow <;> cases first <;> cases second <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, digit, nextBorrow,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_end (borrow : Bool) (before written : List (Option Bool)) :
    evalConfigWithin program (state borrow before [] written) 3 =
      PMF.pure (finish borrow before written) := by
  cases borrow <;>
    simp [evalConfigWithin, stepPMF, next, program, state, finish,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.write, PMF.pure_bind]

private theorem eval_pairs (pairs : List (Bool × Bool)) (borrow : Bool)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state borrow before (BinaryComparison.interleave pairs) written)
        (7 * pairs.length + 3) =
      PMF.pure (finish (borrowOut borrow pairs)
        ((BinaryComparison.interleave pairs).reverse.map some ++ before)
        ((lowerBits borrow pairs).reverse.map some ++ written)) := by
  induction pairs generalizing borrow before written with
  | nil => simpa [borrowOut, lowerBits, BinaryComparison.interleave] using eval_end borrow before written
  | cons pair rest ih =>
      have hBudget : 7 * (pair :: rest).length + 3 = 7 + (7 * rest.length + 3) := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [BinaryComparison.interleave, eval_pair, PMF.pure_bind, ih,
        borrowOut, lowerBits]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private def invalid (before written : List (Option Bool)) : Configuration :=
  { pc := 45, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_odd (borrow : Bool) (before written : List (Option Bool)) (bit : Bool) :
    evalConfigWithin program (state borrow before [bit] written) 5 =
      PMF.pure (invalid (some bit :: before) written) := by
  cases borrow <;> cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, state, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_raw (bits : List Bool) (borrow : Bool)
    (before written : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin program (state borrow before bits written) (7 * (bits.length + 1)) =
        PMF.pure result := by
  match bits with
  | [] =>
      refine ⟨finish borrow before written, rfl, ?_⟩
      change evalConfigWithin program (state borrow before [] written) (3 + 4) = _
      rw [evalConfigWithin_add, eval_end, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [bit] =>
      refine ⟨invalid (some bit :: before) written, rfl, ?_⟩
      change evalConfigWithin program (state borrow before [bit] written) (5 + 9) = _
      rw [evalConfigWithin_add, eval_odd, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | first :: second :: rest =>
      obtain ⟨result, hHalt, hEval⟩ := eval_raw rest (nextBorrow borrow first second)
        (some second :: some first :: before) (some (digit borrow first second) :: written)
      refine ⟨result, hHalt, ?_⟩
      have hBudget : 7 * ((first :: second :: rest).length + 1) =
          7 + (7 * (rest.length + 1) + 7) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_pair, PMF.pure_bind,
        evalConfigWithin_add, hEval, PMF.pure_bind]
      exact eval_halted _ _ hHalt
termination_by bits.length

/-- Odd-length malformed input is rejected in finite time as well. This
certificate measures the original bit code on every raw input. -/
theorem haltsWithin (input : List Bool) : HaltsWithin program input (7 * (input.length + 1)) := by
  obtain ⟨result, hHalt, hEval⟩ := eval_raw input false [] []
  have hInitial : Configuration.initial input = state false [] input [] := by
    cases input <;> rfl
  intro finish run
  have hSupport := (mem_support_evalConfigWithin_iff program _ finish _).mpr run
  rw [hInitial, hEval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalt

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 7 * (length + 1),
    (PolynomiallyBounded.const 7).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- The operational result is the fixed-width difference, with final borrow
recorded in the specification invariant below. -/
theorem eval_interleave (pairs : List (Bool × Bool)) :
    evalWithin program (BinaryComparison.interleave pairs) (7 * pairs.length + 3) =
      PMF.pure (some (differenceBits false pairs)) := by
  have hInitial : Configuration.initial (BinaryComparison.interleave pairs) =
      state false [] (BinaryComparison.interleave pairs) [] := by
    cases BinaryComparison.interleave pairs <;> rfl
  unfold evalWithin
  rw [hInitial, eval_pairs, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits, List.filterMap_append,
    differenceBits]

private theorem differenceBits_cons (borrow first second : Bool) (rest : List (Bool × Bool)) :
    differenceBits borrow ((first, second) :: rest) =
      digit borrow first second :: differenceBits (nextBorrow borrow first second) rest := rfl

/-- The subtraction invariant accounts for the incoming and outgoing borrow.
The finite control stores just one bit. No numerical subtraction instruction
is introduced. -/
theorem differenceBits_invariant (borrow : Bool) (pairs : List (Bool × Bool)) :
    Binary.value (differenceBits borrow pairs) +
      Binary.value (pairs.map Prod.snd) + borrow.toNat =
      Binary.value (pairs.map Prod.fst) + 2 ^ pairs.length * (borrowOut borrow pairs).toNat := by
  induction pairs generalizing borrow with
  | nil => cases borrow <;> simp [differenceBits, lowerBits, borrowOut, Binary.value]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have hDigit : (digit borrow first second).toNat + second.toNat + borrow.toNat =
          first.toNat + 2 * (nextBorrow borrow first second).toNat := by
        cases borrow <;> cases first <;> cases second <;> decide
      have hRest := congrArg (fun x : Nat => 2 * x) (ih (nextBorrow borrow first second))
      simp only [differenceBits_cons, Binary.value, List.map_cons, List.length_cons,
        pow_succ, borrowOut]
      ring_nf at hRest ⊢
      omega

@[simp] theorem differenceBits_length (borrow : Bool) (pairs : List (Bool × Bool)) :
    (differenceBits borrow pairs).length = pairs.length := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair rest ih =>
      change (differenceBits (nextBorrow borrow pair.1 pair.2) rest).length + 1 = rest.length + 1
      rw [ih]

/-- On nonnegative differences the fixed-width result is the exact natural
number difference. Underflow inputs still halt, but have wraparound semantics. -/
theorem differenceBits_value (pairs : List (Bool × Bool))
    (hOrder : Binary.value (pairs.map Prod.snd) ≤ Binary.value (pairs.map Prod.fst)) :
    Binary.value (differenceBits false pairs) =
      Binary.value (pairs.map Prod.fst) - Binary.value (pairs.map Prod.snd) := by
  have hInvariant := differenceBits_invariant false pairs
  have hWidth := Binary.value_lt (differenceBits false pairs)
  rw [differenceBits_length] at hWidth
  cases hBorrow : borrowOut false pairs <;> simp only [hBorrow, Bool.toNat_false,
    Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hInvariant <;> omega

/-- Decoding the actual finite code gives exact subtraction when no underflow
occurs. This theorem is later used by modular reduction. -/
theorem eval_difference (pairs : List (Bool × Bool))
    (hOrder : Binary.value (pairs.map Prod.snd) ≤ Binary.value (pairs.map Prod.fst)) :
    (evalWithin program (BinaryComparison.interleave pairs) (7 * pairs.length + 3)).map
      (Option.map Binary.value) =
      PMF.pure (some
        (Binary.value (pairs.map Prod.fst) - Binary.value (pairs.map Prod.snd))) := by
  rw [eval_interleave, PMF.pure_map]
  simp [differenceBits_value pairs hOrder]

end Machine.BinarySubtraction
