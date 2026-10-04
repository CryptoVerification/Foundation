import Foundation.Machine.BinaryEncoding
import Foundation.Machine.SubroutineProbability
import Foundation.Machine.PolynomialTime

namespace Machine.BinaryComparison

/-- Compare equal-width little-endian numbers presented as alternating
operand bits. A more significant unequal pair overrides the saved comparison.
Only single-cell branches, head moves, and fixed jumps are used. -/
def program : Program :=
  [.branch .input 24 1 4, .moveRight .input, .branch .input 30 18 20,
   .jump 30, .moveRight .input, .branch .input 30 22 18,
   .branch .input 26 7 10, .moveRight .input, .branch .input 30 20 20,
   .jump 30, .moveRight .input, .branch .input 30 22 20,
   .branch .input 28 13 16, .moveRight .input, .branch .input 30 22 20,
   .jump 30, .moveRight .input, .branch .input 30 22 22,
   .moveRight .input, .jump 0,
   .moveRight .input, .jump 6,
   .moveRight .input, .jump 12,
   .write .output false, .halt,
   .write .output true, .halt,
   .write .output false, .halt,
   .erase .output, .halt]

/-- Interleaved operands contain equal numbers of bits. This is a layout
function used to state correctness, not an extra machine instruction. -/
def interleave : List (Bool × Bool) → List Bool
  | [] => []
  | pair :: rest => pair.1 :: pair.2 :: interleave rest

private def address : Ordering → Nat
  | .eq => 0
  | .lt => 6
  | .gt => 12

/-- Lower-bit comparison is retained only when the current bits agree. -/
def update (prior : Ordering) (first second : Bool) : Ordering :=
  if first = second then prior else if first then .gt else .lt

def compare : Ordering → List (Bool × Bool) → Ordering
  | prior, [] => prior
  | prior, pair :: rest => compare (update prior pair.1 pair.2) rest

private def state (prior : Ordering) (before : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { pc := address prior, inputTape := { Tape.ofBits bits with left := before } }

private def finish (comparison : Ordering) (before : List (Option Bool)) : Configuration :=
  { pc := match comparison with | .eq => 25 | .lt => 27 | .gt => 29,
    inputTape := { left := before },
    outputTape := { current := some (comparison == .lt) }, halted := true }

private theorem eval_pair (prior : Ordering) (before : List (Option Bool))
    (first second : Bool) (rest : List Bool) :
    evalConfigWithin program (state prior before (first :: second :: rest)) 5 =
      PMF.pure (state (update prior first second)
        (some second :: some first :: before) rest) := by
  cases prior <;> cases first <;> cases second <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, update,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem eval_end (prior : Ordering) (before : List (Option Bool)) :
    evalConfigWithin program (state prior before []) 3 = PMF.pure (finish prior before) := by
  cases prior <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, finish,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.write, PMF.pure_bind]

private theorem eval_pairs (pairs : List (Bool × Bool)) (prior : Ordering)
    (before : List (Option Bool)) :
    evalConfigWithin program (state prior before (interleave pairs)) (5 * pairs.length + 3) =
      PMF.pure (finish (compare prior pairs)
        ((interleave pairs).reverse.map some ++ before)) := by
  induction pairs generalizing prior before with
  | nil => simpa [compare, interleave] using eval_end prior before
  | cons pair rest ih =>
      have hBudget : 5 * (pair :: rest).length + 3 = 5 + (5 * rest.length + 3) := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [interleave, eval_pair, PMF.pure_bind, ih, compare]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem compare_values (prior : Ordering) (pairs : List (Bool × Bool)) :
    compare prior pairs =
      if Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd) then .lt
      else if Binary.value (pairs.map Prod.snd) < Binary.value (pairs.map Prod.fst) then .gt
      else prior := by
  induction pairs generalizing prior with
  | nil => simp [compare, Binary.value]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      simp only [compare, ih, List.map_cons, Binary.value, update]
      cases first <;> cases second <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, zero_add, eq_self] <;>
        split_ifs <;> first | rfl | omega

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private def invalid (before : List (Option Bool)) : Configuration :=
  { pc := 31, inputTape := { left := before }, halted := true }

private theorem eval_odd (prior : Ordering) (before : List (Option Bool)) (bit : Bool) :
    evalConfigWithin program (state prior before [bit]) 5 =
      PMF.pure (invalid (some bit :: before)) := by
  cases prior <;> cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_raw (bits : List Bool) (prior : Ordering)
    (before : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin program (state prior before bits) (5 * (bits.length + 1)) =
        PMF.pure result := by
  match bits with
  | [] =>
      refine ⟨finish prior before, rfl, ?_⟩
      change evalConfigWithin program (state prior before []) (3 + 2) = _
      rw [evalConfigWithin_add, eval_end, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | [bit] =>
      refine ⟨invalid (some bit :: before), rfl, ?_⟩
      change evalConfigWithin program (state prior before [bit]) (5 + 5) = _
      rw [evalConfigWithin_add, eval_odd, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | first :: second :: rest =>
      obtain ⟨result, hHalt, hEval⟩ := eval_raw rest (update prior first second)
        (some second :: some first :: before)
      refine ⟨result, hHalt, ?_⟩
      have hBudget : 5 * ((first :: second :: rest).length + 1) =
          5 + (5 * (rest.length + 1) + 5) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_pair, PMF.pure_bind,
        evalConfigWithin_add, hEval, PMF.pure_bind]
      exact eval_halted _ _ hHalt
termination_by bits.length

/-- Even an odd-length malformed operand layout halts. The bound is on all
raw inputs and all branches of the original single-cell machine. -/
theorem haltsWithin (input : List Bool) : HaltsWithin program input (5 * (input.length + 1)) := by
  obtain ⟨result, hHalt, hEval⟩ := eval_raw input .eq []
  have hInitial : Configuration.initial input = state .eq [] input := by
    cases input <;> rfl
  intro finish run
  have hSupport := (mem_support_evalConfigWithin_iff program _ finish _).mpr run
  rw [hInitial, hEval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalt

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 5 * (length + 1),
    (PolynomiallyBounded.const 5).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- The actual code returns the accumulated comparison after exactly five
transitions per bit pair and three final transitions. No numerical comparison
is evaluated as an instruction. -/
theorem eval_interleave (pairs : List (Bool × Bool)) :
    evalWithin program (interleave pairs) (5 * pairs.length + 3) =
      PMF.pure (some [compare .eq pairs == .lt]) := by
  have hInitial : Configuration.initial (interleave pairs) = state .eq [] (interleave pairs) := by
    cases interleave pairs <;> rfl
  unfold evalWithin
  rw [hInitial, eval_pairs, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits]

/-- Operational comparison agrees with numerical order on the two
interleaved fixed-width operands. The numerical values occur only in the
correctness statement. -/
theorem eval_lt (pairs : List (Bool × Bool)) :
    evalWithin program (interleave pairs) (5 * pairs.length + 3) =
      PMF.pure (some [decide
        (Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd))]) := by
  rw [eval_interleave, compare_values]
  by_cases h : Binary.value (pairs.map Prod.fst) < Binary.value (pairs.map Prod.snd)
  · simp [h]
  · simp [h]
    split_ifs <;> rfl

end Machine.BinaryComparison
