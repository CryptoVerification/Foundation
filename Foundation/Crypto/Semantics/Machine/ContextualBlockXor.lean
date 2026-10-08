import Foundation.Crypto.Semantics.Machine.DelimitedSampler
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorComponent

/-! Reuse the fixed flagged XOR program with exact saved physical context.
An explicit blank bounds the packet on either side. Arbitrary cells beyond
those boundaries, and beyond the output delimiter, are retained verbatim.
The output frontier has enough explicitly represented blank cells for the
message. This is an entry precondition, not a runtime allocation operation. -/
namespace Machine.FlaggedBlockXor.Contextual
open Foundation.Probability Foundation.Symmetric
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

private def reversePrefix : List Bool → List (Option Bool)
  | [] => []
  | bit :: rest => some bit :: some true :: reversePrefix rest

private theorem messagePrefix_append (first second : List Bool) :
    messagePrefix (first ++ second) = messagePrefix first ++ messagePrefix second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp [messagePrefix, ih]

private theorem reversePrefix_eq (past : List Bool) :
    reversePrefix past = (messagePrefix past.reverse).reverse.map some := by
  induction past with
  | nil => rfl
  | cons bit rest ih =>
      simp [reversePrefix, List.reverse_cons, messagePrefix_append, messagePrefix, ih]

private def writing (past message key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) : Configuration :=
  { inputTape := {OneTimePad.delimitedTape (request message ++ key) inputSuffix with
      left := reversePrefix past ++ none :: inputFrame}
    outputTape := {left := past.map some, right := List.replicate message.length none ++ outputSuffix} }

private theorem write_bit (past key : List Bool) (bit : Bool) (rest : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (writing past (bit :: rest) key inputFrame inputSuffix outputSuffix) 8 =
      PMF.pure (writing (bit :: past) rest key inputFrame inputSuffix outputSuffix) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, code, writing, OneTimePad.delimitedTape, request, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, Tape.write, PMF.pure_bind, List.replicate_succ]

private theorem write_run (past message key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (writing past message key inputFrame inputSuffix outputSuffix) (8 * message.length) =
      PMF.pure (writing (message.reverse ++ past) [] key inputFrame inputSuffix outputSuffix) := by
  induction message generalizing past with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 8 * (bit :: rest).length = 8 + 8 * rest.length by simp; omega,
        evalConfigWithin_add, write_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def backwards (remaining done key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) : Configuration :=
  let suffix := (messagePrefix done ++ false :: key).map some ++ none :: inputSuffix
  { pc := 11
    inputTape := match remaining with
      | [] => {left := inputFrame, right := suffix}
      | bit :: rest =>
          { left := some true :: reversePrefix rest ++ none :: inputFrame
            current := some bit
            right := suffix }
    outputTape := {OneTimePad.delimitedTape done outputSuffix with left := remaining.map some} }

private theorem start_backwards (past key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (writing past [] key inputFrame inputSuffix outputSuffix) 2 =
      PMF.pure (backwards past [] key inputFrame inputSuffix outputSuffix) := by
  cases past <;>
    simp [evalConfigWithin, stepPMF, next, code, writing, OneTimePad.delimitedTape, request, messagePrefix,
      reversePrefix, backwards, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, PMF.pure_bind]

private theorem backward_bit (bit : Bool) (rest done key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (backwards (bit :: rest) done key inputFrame inputSuffix outputSuffix) 5 =
      PMF.pure (backwards rest (bit :: done) key inputFrame inputSuffix outputSuffix) := by
  cases bit <;> cases rest <;> cases done <;>
    simp [evalConfigWithin, stepPMF, next, code, backwards, OneTimePad.delimitedTape, messagePrefix,
      reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, PMF.pure_bind]

private theorem backward_run (remaining done key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (backwards remaining done key inputFrame inputSuffix outputSuffix) (5 * remaining.length) =
      PMF.pure (backwards [] (remaining.reverse ++ done) key inputFrame inputSuffix outputSuffix) := by
  induction remaining generalizing done with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length by simp; omega,
        evalConfigWithin_add, backward_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def scanning (past message key : List Bool) (output : Tape)
    (inputFrame inputSuffix : List (Option Bool)) : Configuration :=
  { pc := 17
    inputTape := {OneTimePad.delimitedTape (request message ++ key) inputSuffix with
      left := reversePrefix past ++ none :: inputFrame}
    outputTape := output }

private theorem start_scanning (message key : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (backwards [] message key inputFrame inputSuffix outputSuffix) 2 =
      PMF.pure (scanning [] message key (OneTimePad.delimitedTape message outputSuffix) inputFrame inputSuffix) := by
  cases message <;>
    simp [evalConfigWithin, stepPMF, next, code, backwards, scanning, OneTimePad.delimitedTape, request,
      messagePrefix, reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, PMF.pure_bind]

private theorem scan_bit (past key : List Bool) (bit : Bool) (rest : List Bool) (output : Tape)
    (inputFrame inputSuffix : List (Option Bool)) :
    evalConfigWithin code (scanning past (bit :: rest) key output inputFrame inputSuffix) 4 =
      PMF.pure (scanning (bit :: past) rest key output inputFrame inputSuffix) := by
  cases rest <;> simp [evalConfigWithin, stepPMF, next, code, scanning, OneTimePad.delimitedTape, request,
    messagePrefix, reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
    Configuration.advance, Tape.moveRight, PMF.pure_bind]

private theorem scan_run (past message key : List Bool) (output : Tape)
    (inputFrame inputSuffix : List (Option Bool)) :
    evalConfigWithin code (scanning past message key output inputFrame inputSuffix) (4 * message.length) =
      PMF.pure (scanning (message.reverse ++ past) [] key output inputFrame inputSuffix) := by
  induction message generalizing past with
  | nil => simp [evalConfigWithin]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length = 4 + 4 * rest.length by simp; omega,
        evalConfigWithin_add, scan_bit, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.append_assoc]

private def xoring (before : List (Option Bool)) (pastKey key pastCipher message : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) : Configuration :=
  { pc := 22
    inputTape := {OneTimePad.delimitedTape key inputSuffix with left := pastKey.reverse.map some ++ before}
    outputTape := {OneTimePad.delimitedTape message outputSuffix with left := pastCipher.reverse.map some} }

private theorem start_xor (past key message : List Bool)
    (inputFrame inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code
      (scanning past [] key (OneTimePad.delimitedTape message outputSuffix) inputFrame inputSuffix) 2 =
      PMF.pure (xoring (some false :: reversePrefix past ++ none :: inputFrame)
        [] key [] message inputSuffix outputSuffix) := by
  cases key <;> cases message <;>
    simp [evalConfigWithin, stepPMF, next, code, scanning, xoring, OneTimePad.delimitedTape, request,
      messagePrefix, reversePrefix, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, PMF.pure_bind]

private theorem xor_bit (before : List (Option Bool)) (pastKey pastCipher : List Bool)
    (key bit : Bool) (keys bits : List Bool) (inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin code (xoring before pastKey (key :: keys) pastCipher (bit :: bits) inputSuffix outputSuffix) 7 =
      PMF.pure (xoring before (pastKey ++ [key]) keys (pastCipher ++ [Bool.xor key bit]) bits
        inputSuffix outputSuffix) := by
  cases key <;> cases bit <;> cases keys <;> cases bits <;>
    simp [evalConfigWithin, stepPMF, next, code, xoring, OneTimePad.delimitedTape, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight,
      Tape.write, PMF.pure_bind, List.reverse_append]

private def xorFinish (before : List (Option Bool)) (key cipher : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) : Configuration :=
  { pc := 36
    inputTape := {left := key.reverse.map some ++ before, right := inputSuffix}
    outputTape := {left := cipher.reverse.map some, right := outputSuffix}
    halted := true }

private theorem xor_run (before : List (Option Bool)) (pastKey pastCipher key message : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) (hLength : key.length = message.length) :
    evalConfigWithin code (xoring before pastKey key pastCipher message inputSuffix outputSuffix)
      (7 * key.length + 2) =
      PMF.pure (xorFinish before (pastKey ++ key) (pastCipher ++ OneTimePad.xorList key message)
        inputSuffix outputSuffix) := by
  induction key generalizing pastKey pastCipher message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp hLength.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, code, xoring, xorFinish, OneTimePad.delimitedTape,
        Instruction.next, Configuration.advance, Configuration.tape, OneTimePad.xorList, PMF.pure_bind]
  | cons bit rest ih =>
      cases message with
      | nil => simp at hLength
      | cons m messages =>
          rw [show 7 * (bit :: rest).length + 2 = 7 + (7 * rest.length + 2) by simp; omega,
            evalConfigWithin_add, xor_bit, PMF.pure_bind, ih _ _ messages (by simpa using hLength)]
          simp [xorFinish, OneTimePad.xorList, List.append_assoc]

private theorem xor_run_before_halt (before : List (Option Bool)) (pastKey pastCipher key message : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) (hLength : key.length = message.length) :
    evalConfigWithin code (xoring before pastKey key pastCipher message inputSuffix outputSuffix)
      (7 * key.length + 1) =
      PMF.pure {xorFinish before (pastKey ++ key) (pastCipher ++ OneTimePad.xorList key message)
        inputSuffix outputSuffix with halted := false} := by
  induction key generalizing pastKey pastCipher message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp hLength.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, code, xoring, xorFinish, OneTimePad.delimitedTape,
        Instruction.next, Configuration.advance, Configuration.tape, OneTimePad.xorList, PMF.pure_bind]
  | cons bit rest ih =>
      cases message with
      | nil => simp at hLength
      | cons m messages =>
          rw [show 7 * (bit :: rest).length + 1 = 7 + (7 * rest.length + 1) by simp; omega,
            evalConfigWithin_add, xor_bit, PMF.pure_bind, ih _ _ messages (by simpa using hLength)]
          simp [xorFinish, OneTimePad.xorList, List.append_assoc]

/-- Context outside the explicitly delimited packet is arbitrary. -/
structure Input where
  key : List Bool
  message : List Bool
  sameLength : key.length = message.length
  inputFrame : List (Option Bool) := []
  inputSuffix : List (Option Bool) := []
  outputSuffix : List (Option Bool) := []

def initial (input : Input) : Configuration :=
  writing [] input.message input.key input.inputFrame input.inputSuffix input.outputSuffix

theorem initial_eq (input : Input) : initial input =
    { inputTape := {OneTimePad.delimitedTape (request input.message ++ input.key) input.inputSuffix with
        left := none :: input.inputFrame}
      outputTape := {right := List.replicate input.message.length none ++ input.outputSuffix} } := rfl

def finish (input : Input) : Configuration :=
  { pc := 36
    inputTape :=
      { left := (request input.message ++ input.key).reverse.map some ++ none :: input.inputFrame
        right := input.inputSuffix }
    outputTape :=
      { left := (OneTimePad.xorList input.key input.message).reverse.map some
        right := input.outputSuffix }
    halted := true }

/-- Exact full-state execution, with unchanged code and arbitrary saved cells. -/
theorem run (input : Input) :
    evalConfigWithin code (initial input) (24 * input.message.length + 8) = PMF.pure (finish input) := by
  rcases input with ⟨key, message, hLength, inputFrame, inputSuffix, outputSuffix⟩
  rw [show 24 * message.length + 8 =
    8 * message.length + (2 + (5 * message.length + (2 + (4 * message.length + (2 + (7 * key.length + 2)))))) by omega,
    evalConfigWithin_add, initial, write_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_backwards, PMF.pure_bind]
  rw [show 5 * message.length = 5 * message.reverse.length by simp,
    evalConfigWithin_add, backward_run, PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [evalConfigWithin_add, start_scanning, PMF.pure_bind, evalConfigWithin_add, scan_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_xor, PMF.pure_bind, xor_run _ [] [] key message inputSuffix outputSuffix hLength]
  simp [xorFinish, finish, reversePrefix_eq, request, List.reverse_append, List.append_assoc]

/-- The immediately preceding state is active, also with arbitrary saved context. -/
theorem run_before_halt (input : Input) :
    evalConfigWithin code (initial input) (24 * input.message.length + 7) =
      PMF.pure {finish input with halted := false} := by
  rcases input with ⟨key, message, hLength, inputFrame, inputSuffix, outputSuffix⟩
  rw [show 24 * message.length + 7 =
    8 * message.length + (2 + (5 * message.length + (2 + (4 * message.length + (2 + (7 * key.length + 1)))))) by omega,
    evalConfigWithin_add, initial, write_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_backwards, PMF.pure_bind]
  rw [show 5 * message.length = 5 * message.reverse.length by simp,
    evalConfigWithin_add, backward_run, PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [evalConfigWithin_add, start_scanning, PMF.pure_bind, evalConfigWithin_add, scan_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [evalConfigWithin_add, start_xor, PMF.pure_bind,
    xor_run_before_halt _ [] [] key message inputSuffix outputSuffix hLength]
  simp [xorFinish, finish, reversePrefix_eq, request, List.reverse_append, List.append_assoc]

/-- A richer entry contract for the existing 37-instruction component. -/
noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed code initial (fun _ output => output) (fun input => PMF.pure (finish input))
    (fun input => 24 * input.message.length + 8)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 37; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

end Machine.FlaggedBlockXor.Contextual
