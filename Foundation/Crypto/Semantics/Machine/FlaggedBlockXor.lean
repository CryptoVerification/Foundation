import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! A fixed two-tape XOR program for a self-delimiting message block followed
by a key block. Each message bit is preceded by true; false terminates the
message block. All copies, scans and head movements are native instructions. -/
namespace Machine.FlaggedBlockXor
open Foundation.Probability Foundation.Symmetric
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

def code : Program :=
  [.branch .input 36 10 1,
   .moveRight .input, .branch .input 36 5 3,
   .write .output true, .jump 7, .write .output false, .jump 7,
   .moveRight .input, .moveRight .output, .jump 0,
   .moveLeft .input, .branch .input 16 12 12,
   .moveLeft .output, .moveLeft .input, .moveLeft .input, .jump 11,
   .moveRight .input, .branch .input 36 21 18,
   .moveRight .input, .moveRight .input, .jump 17,
   .moveRight .input, .branch .input 36 28 23,
   .branch .output 36 24 26, .write .output true, .jump 33,
   .write .output false, .jump 33,
   .branch .output 36 29 31, .write .output false, .jump 33,
   .write .output true, .jump 33,
   .moveRight .input, .moveRight .output, .jump 22, .halt]

def messagePrefix : List Bool → List Bool
  | [] => []
  | bit :: rest => true :: bit :: messagePrefix rest

def request (message : List Bool) := messagePrefix message ++ [false]

private def reversePrefix : List Bool → List (Option Bool)
  | [] => []
  | bit :: rest => some bit :: some true :: reversePrefix rest

private def cells (bits : List Bool) : Tape :=
  ⟨[], (bits.map some ++ [none]).headD none, (bits.map some ++ [none]).tail⟩

private def writing (past message key : List Bool) : Configuration :=
  {inputTape := {cells (request message ++ key) with left := reversePrefix past},
   outputTape := {left := past.map some}}

private theorem write_bit (past key : List Bool) (bit : Bool) (rest : List Bool) :
    evalConfigWithin code (writing past (bit :: rest) key) 8 =
      PMF.pure (writing (bit :: past) rest key) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, code, writing, cells, request, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.write, PMF.pure_bind]

theorem write_run (past message key : List Bool) :
    evalConfigWithin code (writing past message key) (8 * message.length) =
      PMF.pure (writing (message.reverse ++ past) [] key) := by
  induction message generalizing past with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 8 * (bit :: rest).length = 8 + 8 * rest.length by simp; omega,
        evalConfigWithin_add, write_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def backwards (remaining done key : List Bool) : Configuration :=
  let suffix := (messagePrefix done ++ false :: key).map some ++ [none]
  {pc := 11,
   inputTape := match remaining with
     | [] => {right := suffix}
     | bit :: rest => {left := some true :: reversePrefix rest, current := some bit, right := suffix},
   outputTape := {cells done with left := remaining.map some}}

private theorem start_backwards (past key : List Bool) :
    evalConfigWithin code (writing past [] key) 2 = PMF.pure (backwards past [] key) := by
  cases past <;>
    simp [evalConfigWithin, stepPMF, next, code, writing, cells, request, messagePrefix,
      reversePrefix, backwards, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, PMF.pure_bind]

private theorem backward_bit (bit : Bool) (rest done key : List Bool) :
    evalConfigWithin code (backwards (bit :: rest) done key) 5 =
      PMF.pure (backwards rest (bit :: done) key) := by
  cases bit <;> cases rest <;> cases done <;>
    simp [evalConfigWithin, stepPMF, next, code, backwards, cells, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, PMF.pure_bind]

theorem backward_run (remaining done key : List Bool) :
    evalConfigWithin code (backwards remaining done key) (5 * remaining.length) =
      PMF.pure (backwards [] (remaining.reverse ++ done) key) := by
  induction remaining generalizing done with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length by simp; omega,
        evalConfigWithin_add, backward_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def scanning (past message key : List Bool) (output : Tape) : Configuration :=
  {pc := 17, inputTape := {cells (request message ++ key) with left := reversePrefix past ++ [none]},
   outputTape := output}

private theorem start_scanning (message key : List Bool) :
    evalConfigWithin code (backwards [] message key) 2 =
      PMF.pure (scanning [] message key (cells message)) := by
  cases message <;>
    simp [evalConfigWithin, stepPMF, next, code, backwards, scanning, cells, request, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, PMF.pure_bind]

private theorem scan_bit (past key : List Bool) (bit : Bool) (rest : List Bool) (output : Tape) :
    evalConfigWithin code (scanning past (bit :: rest) key output) 4 =
      PMF.pure (scanning (bit :: past) rest key output) := by
  cases rest <;> simp [evalConfigWithin, stepPMF, next, code, scanning, cells, request, messagePrefix,
    reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
    Configuration.advance, Tape.moveRight, PMF.pure_bind]

theorem scan_run (past message key : List Bool) (output : Tape) :
    evalConfigWithin code (scanning past message key output) (4 * message.length) =
      PMF.pure (scanning (message.reverse ++ past) [] key output) := by
  induction message generalizing past with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length = 4 + 4 * rest.length by simp; omega,
        evalConfigWithin_add, scan_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def xoring (before : List (Option Bool)) (pastKey key pastCipher message : List Bool) : Configuration :=
  {pc := 22, inputTape := {cells key with left := pastKey.reverse.map some ++ before},
   outputTape := {cells message with left := pastCipher.reverse.map some}}

private theorem start_xor (past key message : List Bool) :
    evalConfigWithin code (scanning past [] key (cells message)) 2 =
      PMF.pure (xoring (some false :: reversePrefix past ++ [none]) [] key [] message) := by
  cases key <;>
    simp [evalConfigWithin, stepPMF, next, code, scanning, xoring, cells, request, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, PMF.pure_bind]

private theorem xor_bit (before : List (Option Bool)) (pastKey pastCipher : List Bool)
    (key bit : Bool) (keys bits : List Bool) :
    evalConfigWithin code (xoring before pastKey (key :: keys) pastCipher (bit :: bits)) 7 =
      PMF.pure (xoring before (pastKey ++ [key]) keys (pastCipher ++ [Bool.xor key bit]) bits) := by
  cases key <;> cases bit <;> cases keys <;> cases bits <;>
    simp [evalConfigWithin, stepPMF, next, code, xoring, cells, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight,
      Tape.write, PMF.pure_bind, List.reverse_append]

def finish (before : List (Option Bool)) (key cipher : List Bool) : Configuration :=
  {pc := 36, inputTape := {left := key.reverse.map some ++ before},
   outputTape := {left := cipher.reverse.map some}, halted := true}

theorem xor_run (before : List (Option Bool)) (pastKey pastCipher key message : List Bool)
    (hLength : key.length = message.length) :
    evalConfigWithin code (xoring before pastKey key pastCipher message) (7 * key.length + 2) =
      PMF.pure (finish before (pastKey ++ key) (pastCipher ++ Machine.OneTimePad.xorList key message)) := by
  induction key generalizing pastKey pastCipher message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp hLength.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, code, xoring, finish, cells, Instruction.next,
        Configuration.advance, Configuration.tape, Machine.OneTimePad.xorList, PMF.pure_bind]
  | cons bit rest ih =>
      cases message with
      | nil => simp at hLength
      | cons m messages =>
          rw [show 7 * (bit :: rest).length + 2 = 7 + (7 * rest.length + 2) by simp; omega,
            evalConfigWithin_add, xor_bit, PMF.pure_bind, ih _ _ messages (by simpa using hLength)]
          simp [finish, Machine.OneTimePad.xorList, List.append_assoc]

private theorem xor_run_before_halt (before : List (Option Bool)) (pastKey pastCipher key message : List Bool)
    (hLength : key.length = message.length) :
    evalConfigWithin code (xoring before pastKey key pastCipher message) (7 * key.length + 1) =
      PMF.pure {finish before (pastKey ++ key)
        (pastCipher ++ Machine.OneTimePad.xorList key message) with halted := false} := by
  induction key generalizing pastKey pastCipher message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp hLength.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, code, xoring, finish, cells, Instruction.next,
        Configuration.advance, Configuration.tape, Machine.OneTimePad.xorList, PMF.pure_bind]
  | cons bit rest ih =>
      cases message with
      | nil => simp at hLength
      | cons m messages =>
          rw [show 7 * (bit :: rest).length + 1 = 7 + (7 * rest.length + 1) by simp; omega,
            evalConfigWithin_add, xor_bit, PMF.pure_bind, ih _ _ messages (by simpa using hLength)]
          simp [finish, Machine.OneTimePad.xorList, List.append_assoc]

def initial (key message : List Bool) : Configuration := writing [] message key

def final (key message : List Bool) : Configuration :=
  finish (some false :: reversePrefix message.reverse ++ [none]) key
    (Machine.OneTimePad.xorList key message)

@[simp] theorem final_halted (key message : List Bool) : (final key message).halted = true := rfl

@[simp] theorem final_output (key message : List Bool) :
    (final key message).outputBits = Machine.OneTimePad.xorList key message := by
  simp [final, finish, Configuration.outputBits, Tape.bits]

theorem final_outputTape (key message : List Bool) :
    (final key message).outputTape = {left := (Machine.OneTimePad.xorList key message).reverse.map some} := rfl

@[simp] theorem request_length (message : List Bool) : (request message).length = 2 * message.length + 1 := by
  have hp : (messagePrefix message).length = 2 * message.length := by
    induction message with
    | nil => rfl
    | cons bit rest ih => simp [messagePrefix, ih]; omega
  simp [request, hp]

theorem run (key message : List Bool) (hLength : key.length = message.length) :
    evalConfigWithin code (initial key message) (24 * message.length + 8) =
      PMF.pure (finish (some false :: reversePrefix message.reverse ++ [none]) key
        (Machine.OneTimePad.xorList key message)) := by
  rw [show 24 * message.length + 8 =
    8 * message.length + (2 + (5 * message.length + (2 + (4 * message.length + (2 + (7 * key.length + 2)))))) by omega,
    evalConfigWithin_add, initial, write_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_backwards, PMF.pure_bind]
  rw [show 5 * message.length = 5 * message.reverse.length by simp,
    evalConfigWithin_add, backward_run, PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [evalConfigWithin_add, start_scanning, PMF.pure_bind,
    evalConfigWithin_add, scan_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_xor, PMF.pure_bind, xor_run _ [] [] key message hLength]
  simp

/-- The exact preceding horizon is active, so the existing final run does
not hide an earlier halt followed by absorbing padding. -/
theorem run_before_halt (key message : List Bool) (hLength : key.length = message.length) :
    evalConfigWithin code (initial key message) (24 * message.length + 7) =
      PMF.pure {final key message with halted := false} := by
  rw [show 24 * message.length + 7 =
    8 * message.length + (2 + (5 * message.length + (2 + (4 * message.length + (2 + (7 * key.length + 1)))))) by omega,
    evalConfigWithin_add, initial, write_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_backwards, PMF.pure_bind]
  rw [show 5 * message.length = 5 * message.reverse.length by simp,
    evalConfigWithin_add, backward_run, PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [evalConfigWithin_add, start_scanning, PMF.pure_bind,
    evalConfigWithin_add, scan_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_xor, PMF.pure_bind, xor_run_before_halt _ [] [] key message hLength]
  simp [final]

namespace Layout

private theorem reversePrefix_append (first second : List Bool) :
    reversePrefix (first ++ second) = reversePrefix first ++ reversePrefix second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp [reversePrefix, ih]

private theorem reverse_message (message : List Bool) :
    reversePrefix message.reverse = (messagePrefix message).reverse.map some := by
  induction message with
  | nil => rfl
  | cons bit rest ih =>
      simp [List.reverse_cons, reversePrefix_append, reversePrefix, ih,
        messagePrefix, List.map_append, List.append_assoc]

/-- Exact retained scratch cells at exit, for charged cleanup by callers. -/
theorem final_inputTape (key message : List Bool) : (final key message).inputTape =
    {left := (request message ++ key).reverse.map some ++ [none]} := by
  simp [final, finish, reverse_message, request, List.reverse_append, List.map_append, List.append_assoc]

end Layout
end Machine.FlaggedBlockXor
