import Foundation.Constructions.Symmetric.EncryptThenMAC.Semantics
import Foundation.Constructions.Symmetric.OneTimePadNative

/-! A finite native implementation of a two-entry authentication table.
Ciphertexts are bits; tags have the public width. The implementation selects
one of two independently stored secret rows. This module proves computation
and resource bounds, not unforgeability for an unrestricted signing oracle. -/
namespace Foundation.Symmetric.EncryptThenMAC.TableMAC

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

abbrev Key (width : Nat) := Bits width × Bits width

/-- The native sampler's interleaved output represents the two table rows. -/
def splitKey {width : Nat} (bits : Bits (2 * width)) : Key width :=
  (fun i => bits ⟨2 * i.val, by omega⟩,
   fun i => bits ⟨2 * i.val + 1, by omega⟩)

def sign {width : Nat} (key : Key width) (ciphertext : Bool) : Bits width :=
  if ciphertext then key.2 else key.1

noncomputable def scheme (width : Nat → Nat) : MAC (fun _ => Bool) where
  Key := fun n => Key (width n)
  Tag := fun n => Bits (width n)
  keygen := fun n => (uniform (Bits (2 * width n))).map splitKey
  sign := fun _ key ciphertext => sign key ciphertext
  verify := fun _ key ciphertext tag => decide (sign key ciphertext = tag)
  correctness := by intro n key ciphertext; simp

theorem pairInput_ofFn {width : Nat} (first second : Bits width) :
    Machine.OneTimePad.pairInput first.toList second.toList =
      (List.ofFn (fun i => [first i, second i])).flatten := by
  induction width with
  | zero => simp [Bits.toList, Machine.OneTimePad.pairInput]
  | succ width ih =>
      simp only [Bits.toList, List.ofFn_succ, Machine.OneTimePad.pairInput,
        List.flatten_cons, List.cons_append, List.nil_append]
      exact congrArg (first 0 :: second 0 :: ·) (ih (fun i => first i.succ) (fun i => second i.succ))

/-- Splitting the sampler output and encoding the two rows changes no bits. -/
theorem splitKey_encoding {width : Nat} (bits : Bits (2 * width)) :
    Machine.OneTimePad.pairInput (splitKey bits).1.toList (splitKey bits).2.toList = bits.toList := by
  rw [pairInput_ofFn]
  unfold Bits.toList
  conv_rhs => rw [List.ofFn_mul']
  rfl

namespace Native
open Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-- The first input cell chooses a row. The remaining cells are interleaved
row pairs. Every bit read, write, movement, branch, and jump is an instruction. -/
def signCode : Program :=
  [.branch .input 25 1 14,
   .moveRight .input,
   .branch .input 25 3 7,
   .moveRight .input, .branch .input 25 5 5, .write .output false, .jump 11,
   .moveRight .input, .branch .input 25 9 9, .write .output true, .jump 11,
   .moveRight .input, .moveRight .output, .jump 2,
   .moveRight .input,
   .branch .input 25 16 16, .moveRight .input,
   .branch .input 25 18 20,
   .write .output false, .jump 22, .write .output true, .jump 22,
   .moveRight .input, .moveRight .output, .jump 15, .halt]

abbrev state (side : Bool) (pastInput pastOutput remaining : List Bool) : Configuration :=
  { Machine.OneTimePad.state pastInput pastOutput remaining with pc := if side then 15 else 2 }

abbrev finish (pastInput pastOutput : List Bool) : Configuration :=
  Machine.OneTimePad.finish 25 pastInput pastOutput

/-- Both row branches consume two input cells in eight transitions. -/
theorem iteration (side first second : Bool) (pastInput pastOutput rest : List Bool) :
    evalConfigWithin signCode (state side pastInput pastOutput (first :: second :: rest)) 8 =
      PMF.pure (state side (pastInput ++ [first, second])
        (pastOutput ++ [if side then second else first]) rest) := by
  cases side <;> cases first <;> cases second <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, signCode, state, Machine.OneTimePad.state,
      Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append]

theorem rows_run (side : Bool) (pastInput pastOutput first second : List Bool)
    (h : first.length = second.length) :
    evalConfigWithin signCode
      (state side pastInput pastOutput (Machine.OneTimePad.pairInput first second))
      (8 * first.length + 2) =
      PMF.pure (finish (pastInput ++ Machine.OneTimePad.pairInput first second)
        (pastOutput ++ if side then second else first)) := by
  induction first generalizing pastInput pastOutput second with
  | nil =>
      have hs : second = [] := List.length_eq_zero_iff.mp h.symm
      subst second
      cases side <;>
        simp [evalConfigWithin, stepPMF, next, signCode, state, finish,
          Machine.OneTimePad.state, Machine.OneTimePad.finish, Machine.OneTimePad.pairInput,
          Tape.ofBits, Instruction.next, Configuration.tape]
  | cons bit first ih =>
      cases second with
      | nil => simp at h
      | cons other second =>
          rw [show 8 * (bit :: first).length + 2 = 8 + (8 * first.length + 2) by simp; omega,
            Machine.OneTimePad.pairInput, evalConfigWithin_add, iteration, PMF.pure_bind,
            ih _ _ second (by simpa using h)]
          cases side <;> simp [Machine.OneTimePad.pairInput, List.append_assoc]

theorem initialization_steps (side : Bool) (rows : List Bool) :
    evalConfigWithin signCode (Configuration.initial (side :: rows)) 2 =
      PMF.pure (state side [side] [] rows) := by
  cases side <;> cases rows <;>
    simp [evalConfigWithin, stepPMF, next, signCode, state, Machine.OneTimePad.state,
      Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
      Configuration.updateTape, Configuration.advance, Tape.moveRight]

/-- A caller can retain earlier input cells and an output prefix. The
subroutine consumes only the remaining key rows and appends the selected tag. -/
theorem initialization_from (side : Bool) (pastInput pastOutput rows : List Bool) :
    evalConfigWithin signCode (Machine.OneTimePad.state pastInput pastOutput (side :: rows)) 2 =
      PMF.pure (state side (pastInput ++ [side]) pastOutput rows) := by
  cases side <;> cases rows <;>
    simp [evalConfigWithin, stepPMF, next, signCode, state, Machine.OneTimePad.state,
      Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, List.reverse_append]

theorem sign_from_run {width : Nat} (key : Key width) (ciphertext : Bool)
    (pastInput pastOutput : List Bool) :
    evalConfigWithin signCode
      (Machine.OneTimePad.state pastInput pastOutput
        (ciphertext :: Machine.OneTimePad.pairInput key.1.toList key.2.toList)) (8 * width + 4) =
      PMF.pure (finish (pastInput ++ ciphertext :: Machine.OneTimePad.pairInput key.1.toList key.2.toList)
        (pastOutput ++ (sign key ciphertext).toList)) := by
  rw [show 8 * width + 4 = 2 + (8 * width + 2) by omega,
    evalConfigWithin_add, initialization_from, PMF.pure_bind]
  have h := rows_run ciphertext (pastInput ++ [ciphertext]) pastOutput
    key.1.toList key.2.toList (by simp)
  simp only [Bits.length_toList] at h
  rw [h]
  cases ciphertext <;> simp [sign, List.append_assoc]

def input {width : Nat} (key : Key width) (ciphertext : Bool) : List Bool :=
  ciphertext :: Machine.OneTimePad.pairInput key.1.toList key.2.toList

/-- Exact deterministic output for a fixed code at every public width. -/
theorem sign_correct {width : Nat} (key : Key width) (ciphertext : Bool) :
    evalWithin signCode (input key ciphertext) (8 * width + 4) =
      PMF.pure (some (sign key ciphertext).toList) := by
  unfold evalWithin input
  rw [show 8 * width + 4 = 2 + (8 * width + 2) by omega,
    evalConfigWithin_add, initialization_steps, PMF.pure_bind]
  have h := rows_run ciphertext [ciphertext] [] key.1.toList key.2.toList (by simp)
  simp only [Bits.length_toList] at h
  rw [h, PMF.pure_map]
  cases ciphertext <;>
    simp [finish, Machine.OneTimePad.finish, Machine.OneTimePad.state,
      Configuration.outputBits, Tape.bits, sign]

/-- All coin branches of the signer halt on valid typed inputs. -/
theorem sign_halts {width : Nat} (key : Key width) (ciphertext : Bool) :
    HaltsWithin signCode (input key ciphertext) (8 * width + 4) := by
  apply haltsWithin_of_no_timeout_support
  rw [sign_correct]
  simp

@[simp] theorem input_length {width : Nat} (key : Key width) (ciphertext : Bool) :
    (input key ciphertext).length = 2 * width + 1 := by
  simp only [input, List.length_cons]
  rw [Machine.OneTimePad.pairInput_length _ _ (by simp)]
  simp

/-- Total parsing ignores an incomplete final row pair. -/
def selectedPairs (side : Bool) : List Bool → List Bool
  | first :: second :: rest => (if side then second else first) :: selectedPairs side rest
  | _ => []

theorem all_rows_run (side : Bool) (pastInput pastOutput rows : List Bool) :
    evalConfigWithin signCode (state side pastInput pastOutput rows) (4 * rows.length + 4) =
      PMF.pure (finish (pastInput ++ rows) (pastOutput ++ selectedPairs side rows)) := by
  induction rows using List.twoStepInduction generalizing pastInput pastOutput with
  | nil =>
      cases side <;>
        simp [evalConfigWithin, stepPMF, next, signCode, state, finish,
          Machine.OneTimePad.state, Machine.OneTimePad.finish, selectedPairs,
          Tape.ofBits, Instruction.next, Configuration.tape]
  | singleton bit =>
      cases side <;> cases bit <;>
        simp [evalConfigWithin, stepPMF, next, signCode, state, finish,
          Machine.OneTimePad.state, Machine.OneTimePad.finish, selectedPairs,
          Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
          Configuration.advance, Tape.moveRight, List.reverse_append]
  | cons_cons first second rest ih =>
      rw [show 4 * (first :: second :: rest).length + 4 = 8 + (4 * rest.length + 4) by simp; omega,
        evalConfigWithin_add, iteration, PMF.pure_bind, ih]
      simp [selectedPairs, List.append_assoc]

theorem all_from_run (side : Bool) (pastInput pastOutput rows : List Bool) :
    evalConfigWithin signCode (Machine.OneTimePad.state pastInput pastOutput (side :: rows))
      (4 * rows.length + 6) =
      PMF.pure (finish (pastInput ++ side :: rows) (pastOutput ++ selectedPairs side rows)) := by
  rw [show 4 * rows.length + 6 = 2 + (4 * rows.length + 4) by omega,
    evalConfigWithin_add, initialization_from, PMF.pure_bind, all_rows_run]
  simp [List.append_assoc]

/-- A malformed packet still has a concrete all-branch stopping bound. -/
theorem all_output (raw : List Bool) :
    evalWithin signCode raw (4 * raw.length + 6) =
      PMF.pure (some (match raw with | [] => [] | side :: rows => selectedPairs side rows)) := by
  cases raw with
  | nil =>
      simp [evalWithin, evalConfigWithin, stepPMF, next, signCode, Configuration.initial,
        Tape.ofBits, Instruction.next, Configuration.tape, Configuration.outputBits, Tape.bits, PMF.pure_map]
  | cons side rows =>
      rw [evalWithin, show 4 * (side :: rows).length + 6 = 2 + (4 * rows.length + 8) by simp; omega]
      rw [show 4 * rows.length + 8 = (4 * rows.length + 4) + 4 by omega,
        evalConfigWithin_add, initialization_steps, PMF.pure_bind,
        evalConfigWithin_add, all_rows_run, PMF.pure_bind]
      cases side <;>
        simp [evalConfigWithin, stepPMF, next, finish, Machine.OneTimePad.finish,
          Machine.OneTimePad.state, Configuration.outputBits, Tape.bits, PMF.pure_map]

theorem all_halts (raw : List Bool) : HaltsWithin signCode raw (4 * raw.length + 6) := by
  apply haltsWithin_of_no_timeout_support
  rw [all_output]
  simp

theorem time_polynomial : PolynomiallyBounded (fun n => 4 * n + 6) :=
  ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 6)

def signProgram : CryptoLogic.BoundedProgram where
  program := signCode
  budget := fun n => 4 * n + 6
  polynomial := time_polynomial
  halts := all_halts

/-- The actual finite sampler outputs exactly the table-key distribution.
The output codec merely names the two rows; it changes no emitted bits. -/
theorem keygen_correct (width : Nat → Nat) (n : Nat) :
    Machine.evalWithin OneTimePad.Native.keygenCode (List.replicate (2 * width n) true)
      (5 * (2 * width n) + 2) =
      ((scheme width).keygen n).map (fun key => some
        (Machine.OneTimePad.pairInput key.1.toList key.2.toList)) := by
  rw [OneTimePad.Native.keygen_uniform]
  simp only [scheme, PMF.map_comp, Function.comp_def, splitKey_encoding]

def keygenProgram : CryptoLogic.BoundedProgram := OneTimePad.Native.keygenProgram

theorem keygen_profile_polynomial {width : Nat → Nat} (h : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 5 * (2 * width n) + 2) :=
  ((PolynomiallyBounded.const 5).mul ((PolynomiallyBounded.const 2).mul h)).add
    (PolynomiallyBounded.const 2)

theorem sign_profile_polynomial {width : Nat → Nat} (h : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 8 * width n + 4) :=
  ((PolynomiallyBounded.const 8).mul h).add (PolynomiallyBounded.const 4)

end Native
end Foundation.Symmetric.EncryptThenMAC.TableMAC
