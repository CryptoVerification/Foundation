import Foundation.Crypto.Semantics.Machine.NativeUniformSequence
import Foundation.Crypto.Semantics.Machine.FiniteRandomness

/-! Write fresh fair bits to private input cells, then rewind to their first cell.
All movement and return instructions are included in the stopping bound. -/
namespace Machine.NativeBitGenerator
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def coin : Program := [.randomBit .input, .moveRight .input, .halt]
def back : Program := [.moveLeft .input, .halt]

def code : ℕ → Program
  | 0 => [.halt]
  | n + 1 => coin.followedBy ((code n).followedBy back)

def blankBlock : ℕ → Tape → Tape
  | 0, suffix => suffix
  | n + 1, suffix =>
    {left := suffix.left, right := List.replicate n none ++ suffix.current :: suffix.right}

theorem afterRead_blankBlock (word : List Bool) (n : ℕ) (suffix : Tape) :
    afterRead word (blankBlock n suffix) = blankBlock n (afterRead word suffix) := by
  cases n <;> rfl

theorem blankBlock_written_move (n : ℕ) (suffix : Tape) (bit : Bool) :
    ((blankBlock (n + 1) suffix).write (some bit)).moveRight =
      blankBlock n {suffix with left := some bit :: suffix.left} := by
  cases n <;> simp [blankBlock, List.replicate_succ, Tape.write, Tape.moveRight]

theorem preload_moveLeft_cons (bit : Bool) (bits : List Bool) (suffix : Tape) :
    (preload bits {suffix with left := some bit :: suffix.left}).moveLeft =
      preload (bit :: bits) suffix := by
  cases bits <;> simp [preload, Tape.moveLeft]

def coinFinish (bit : Bool) (input output : Tape) : Configuration :=
  {pc := 2, inputTape := (input.write (some bit)).moveRight, outputTape := output, halted := true}

theorem coin_run (input output : Tape) :
    evalConfigWithin coin (NativeBitChoice.start input output) 3 =
      sampleBit.map (fun bit => coinFinish bit input output) := by
  have hFirst : stepPMF coin (NativeBitChoice.start input output) =
      sampleBit.map (fun bit =>
        ({pc := 1, inputTape := input.write (some bit), outputTape := output} : Configuration)) := by
    simp only [stepPMF, next, coin, NativeBitChoice.start, Bool.false_eq_true, ↓reduceIte,
      List.getElem?_cons_zero, Instruction.next]
    congr 1
    funext bit
    cases bit <;> rfl
  rw [evalConfigWithin_succ_head, hFirst, PMF.bind_map]
  have hTail (bit : Bool) : evalConfigWithin coin
      ({pc := 1, inputTape := input.write (some bit), outputTape := output} : Configuration) 2 =
        PMF.pure (coinFinish bit input output) := by
    simp [evalConfigWithin, stepPMF, next, coin, Instruction.next,
      Configuration.updateTape, Configuration.advance, coinFinish]
  simp only [Function.comp_def, hTail]
  rfl

theorem coin_stops : StopsEverywhere coin 3 := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [coin_run, PMF.mem_support_map_iff] at member
  obtain ⟨bit, _, rfl⟩ := member
  rfl

theorem back_run (input output : Tape) :
    evalConfigWithin back (NativeBitChoice.start input output) 2 =
      PMF.pure
        ({pc := 1, inputTape := input.moveLeft, outputTape := output, halted := true} : Configuration) := by
  simp [evalConfigWithin, stepPMF, next, back, NativeBitChoice.start, Instruction.next,
    Configuration.updateTape, Configuration.advance]

theorem back_stops : StopsEverywhere back 2 := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [back_run, PMF.mem_support_pure_iff] at member
  subst finish
  rfl

theorem code_length (n : ℕ) : (code n).length = 11 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [code, NativeUniformSequence.code_length, ih, coin, back,
      List.length_cons, List.length_nil]
    omega

theorem code_stops (n : ℕ) : StopsEverywhere (code n) (7 * n + 1) := by
  induction n with
  | zero =>
    intro input output finish trace
    have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    have h : evalConfigWithin (code 0) (NativeBitChoice.start input output) 1 =
        PMF.pure
          ({pc := 0, inputTape := input, outputTape := output, halted := true} : Configuration) := by
      simp [code, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next]
    rw [h, PMF.mem_support_pure_iff] at member
    subst finish
    rfl
  | succ n ih =>
    have hRest := NativeUniformSequence.stops (code n) back (7 * n + 1) 2 ih back_stops
    have hWhole := NativeUniformSequence.stops coin ((code n).followedBy back)
      3 ((7 * n + 1) + 2 + 1) coin_stops hRest
    have hTime : 3 + ((7 * n + 1) + 2 + 1) + 1 = 7 * (n + 1) + 1 := by omega
    rw [hTime] at hWhole
    exact hWhole

def finish (n : ℕ) (bits : Fin n → Bool) (suffix output : Tape) : Configuration :=
  {pc := 11 * n, inputTape := preload (List.ofFn bits) suffix,
    outputTape := output, halted := true}

theorem run (n : ℕ) (suffix output : Tape) :
    evalConfigWithin (code n) (NativeBitChoice.start (blankBlock n suffix) output) (7 * n + 1) =
      (uniform (Fin n → Bool)).map (fun bits => finish n bits suffix output) := by
  induction n generalizing suffix output with
  | zero =>
    simp [code, blankBlock, finish, List.ofFn_zero, preload, evalConfigWithin,
      stepPMF, next, NativeBitChoice.start, Instruction.next, PMF.map_const, Function.const_def]
  | succ n ih =>
    have hRest := NativeUniformSequence.stops (code n) back (7 * n + 1) 2
      (code_stops n) back_stops
    have hTail (bit : Bool) :
        evalConfigWithin ((code n).followedBy back)
          (NativeBitChoice.start (blankBlock n {suffix with left := some bit :: suffix.left}) output)
          ((7 * n + 1) + 2 + 1) =
        (uniform (Fin n → Bool)).map (fun tail =>
          ({pc := (code n).length + back.length + 2,
            inputTape := preload (List.ofFn (Fin.cons bit tail)) suffix,
            outputTape := output, halted := true} : Configuration)) := by
      rw [NativeUniformSequence.run _ _ _ _ (code_stops n) back_stops, ih, PMF.bind_map]
      have hBack (tail : Fin n → Bool) :
          evalConfigWithin back
            ((finish n tail {suffix with left := some bit :: suffix.left} output).resumeAt 0) 2 =
          PMF.pure
            ({pc := 1, inputTape := (preload (List.ofFn tail)
                {suffix with left := some bit :: suffix.left}).moveLeft,
              outputTape := output, halted := true} : Configuration) :=
        back_run _ _
      simp [Function.comp_def, hBack, PMF.pure_map, List.ofFn_succ,
        preload_moveLeft_cons]
      rfl
    have hTailStart (bit : Bool) :
        (coinFinish bit (blankBlock (n + 1) suffix) output).resumeAt 0 =
        NativeBitChoice.start (blankBlock n {suffix with left := some bit :: suffix.left}) output := by
      simp [coinFinish, Configuration.resumeAt, NativeBitChoice.start, blankBlock_written_move]
    rw [show 7 * (n + 1) + 1 = 3 + ((7 * n + 1) + 2 + 1) + 1 by omega,
      code, NativeUniformSequence.run _ _ _ _ coin_stops hRest, coin_run, PMF.bind_map]
    rw [← uniform_bits_cons, PMF.map_bind]
    congr 1
    funext bit
    simp only [Function.comp_def, hTailStart]
    rw [hTail, PMF.map_comp, PMF.map_comp]
    congr 1
    funext tail
    simp [finish, code_length, NativeUniformSequence.code_length,
      coin, back, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm]
    omega

end Machine.NativeBitGenerator
