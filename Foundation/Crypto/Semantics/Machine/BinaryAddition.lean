import Foundation.Crypto.Semantics.Machine.BinaryComparison

namespace Machine.BinaryAddition

/-- Ripple-carry addition on interleaved little-endian input. Carry is one
finite-control bit; every output write and both head moves are actual steps. -/
def program : Program :=
  [.branch .input 40 1 4, .moveRight .input, .branch .input 44 6 11,
   .jump 44, .moveRight .input, .branch .input 44 11 16,
   .write .output false, .moveRight .input, .moveRight .output, .jump 0,
   .halt,
   .write .output true, .moveRight .input, .moveRight .output, .jump 0,
   .halt,
   .write .output false, .moveRight .input, .moveRight .output, .jump 20,
   .branch .input 42 21 24, .moveRight .input, .branch .input 44 11 26,
   .jump 44, .moveRight .input, .branch .input 44 26 31,
   .write .output false, .moveRight .input, .moveRight .output, .jump 20,
   .halt,
   .write .output true, .moveRight .input, .moveRight .output, .jump 20,
   .halt, .halt, .halt, .halt, .halt,
   .erase .output, .halt, .write .output true, .halt,
   .erase .output, .halt]

def digit (carry first second : Bool) : Bool := carry.xor (first.xor second)
def nextCarry (carry first second : Bool) : Bool :=
  (first && second) || (carry && (first || second))

def lowerBits : Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | carry, pair :: rest => digit carry pair.1 pair.2 ::
      lowerBits (nextCarry carry pair.1 pair.2) rest

def carryOut : Bool → List (Bool × Bool) → Bool
  | carry, [] => carry
  | carry, pair :: rest => carryOut (nextCarry carry pair.1 pair.2) rest

def sumBits (carry : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  lowerBits carry pairs ++ if carryOut carry pairs then [true] else []

private def state (carry : Bool) (before : List (Option Bool)) (bits : List Bool)
    (written : List (Option Bool)) : Configuration :=
  { pc := if carry then 20 else 0,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { left := written } }

private def finish (carry : Bool) (before written : List (Option Bool)) : Configuration :=
  { pc := if carry then 43 else 41,
    inputTape := { left := before },
    outputTape := { left := written, current := if carry then some true else none },
    halted := true }

private theorem eval_pair (carry : Bool) (before written : List (Option Bool))
    (first second : Bool) (rest : List Bool) :
    evalConfigWithin program (state carry before (first :: second :: rest) written) 7 =
      PMF.pure (state (nextCarry carry first second)
        (some second :: some first :: before) rest (some (digit carry first second) :: written)) := by
  cases carry <;> cases first <;> cases second <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, digit, nextCarry,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_end (carry : Bool) (before written : List (Option Bool)) :
    evalConfigWithin program (state carry before [] written) 3 =
      PMF.pure (finish carry before written) := by
  cases carry <;>
    simp [evalConfigWithin, stepPMF, next, program, state, finish,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.write, PMF.pure_bind]

private theorem eval_pairs (pairs : List (Bool × Bool)) (carry : Bool)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state carry before (BinaryComparison.interleave pairs) written)
        (7 * pairs.length + 3) =
      PMF.pure (finish (carryOut carry pairs)
        ((BinaryComparison.interleave pairs).reverse.map some ++ before)
        ((lowerBits carry pairs).reverse.map some ++ written)) := by
  induction pairs generalizing carry before written with
  | nil => simpa [carryOut, lowerBits, BinaryComparison.interleave] using eval_end carry before written
  | cons pair rest ih =>
      have hBudget : 7 * (pair :: rest).length + 3 = 7 + (7 * rest.length + 3) := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [BinaryComparison.interleave, eval_pair, PMF.pure_bind, ih,
        carryOut, lowerBits]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private def invalid (before written : List (Option Bool)) : Configuration :=
  { pc := 45, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_odd (carry : Bool) (before written : List (Option Bool)) (bit : Bool) :
    evalConfigWithin program (state carry before [bit] written) 5 =
      PMF.pure (invalid (some bit :: before) written) := by
  cases carry <;> cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, state, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_raw (bits : List Bool) (carry : Bool)
    (before written : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin program (state carry before bits written) (7 * (bits.length + 1)) =
        PMF.pure result := by
  match bits with
  | [] =>
      refine ⟨finish carry before written, rfl, ?_⟩
      change evalConfigWithin program (state carry before [] written) (3 + 4) = _
      rw [evalConfigWithin_add, eval_end, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [bit] =>
      refine ⟨invalid (some bit :: before) written, rfl, ?_⟩
      change evalConfigWithin program (state carry before [bit] written) (5 + 9) = _
      rw [evalConfigWithin_add, eval_odd, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | first :: second :: rest =>
      obtain ⟨result, hHalt, hEval⟩ := eval_raw rest (nextCarry carry first second)
        (some second :: some first :: before) (some (digit carry first second) :: written)
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

/-- The operational result includes the final carry when it is nonzero. -/
theorem eval_interleave (pairs : List (Bool × Bool)) :
    evalWithin program (BinaryComparison.interleave pairs) (7 * pairs.length + 3) =
      PMF.pure (some (sumBits false pairs)) := by
  have hInitial : Configuration.initial (BinaryComparison.interleave pairs) =
      state false [] (BinaryComparison.interleave pairs) [] := by
    cases BinaryComparison.interleave pairs <;> rfl
  unfold evalWithin
  rw [hInitial, eval_pairs, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits, List.filterMap_append,
    sumBits]
  cases carryOut false pairs <;> simp

private theorem sumBits_cons (carry first second : Bool) (rest : List (Bool × Bool)) :
    sumBits carry ((first, second) :: rest) =
      digit carry first second :: sumBits (nextCarry carry first second) rest := rfl

/-- Numerical arithmetic appears in the specification, never as a machine
instruction. The invariant accounts for the incoming carry. -/
theorem sumBits_value (carry : Bool) (pairs : List (Bool × Bool)) :
    Binary.value (sumBits carry pairs) =
      Binary.value (pairs.map Prod.fst) + Binary.value (pairs.map Prod.snd) + carry.toNat := by
  induction pairs generalizing carry with
  | nil => cases carry <;> simp [sumBits, lowerBits, carryOut, Binary.value]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      rw [sumBits_cons]
      simp only [Binary.value, List.map_cons, ih]
      cases carry <;> cases first <;> cases second <;>
        simp [digit, nextCarry] <;> omega

/-- Decoding the output of the actual finite program gives the exact sum. -/
theorem eval_sum (pairs : List (Bool × Bool)) :
    (evalWithin program (BinaryComparison.interleave pairs) (7 * pairs.length + 3)).map
      (Option.map Binary.value) =
      PMF.pure (some
        (Binary.value (pairs.map Prod.fst) + Binary.value (pairs.map Prod.snd))) := by
  rw [eval_interleave, PMF.pure_map]
  simp [sumBits_value]

end Machine.BinaryAddition
