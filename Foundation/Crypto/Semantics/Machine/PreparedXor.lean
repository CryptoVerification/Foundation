import Foundation.Crypto.Semantics.Machine.PairPreparation
import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! The existing finite XOR program runs on the physical delimited buffer
produced by input preparation. All trailing cells and complete endpoints
are retained; no canonicalization of represented blanks is performed. -/
namespace Machine.OneTimePad.Prepared
open Foundation.Probability Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def state (pastInput pastOutput remaining : List Bool) (tail : List (Option Bool)) : Configuration :=
  { inputTape := PairPreparation.operand pastInput remaining tail,
    outputTape := { left := pastOutput.reverse.map some } }

def finish (pastInput pastOutput : List Bool) (tail : List (Option Bool)) : Configuration :=
  { state pastInput pastOutput [] tail with pc := 16, halted := true }

theorem iteration (pastInput pastOutput rest : List Bool) (key message : Bool)
    (tail : List (Option Bool)) :
    evalConfigWithin xorCode (state pastInput pastOutput (key :: message :: rest) tail) 8 =
      PMF.pure (state (pastInput ++ [key, message]) (pastOutput ++ [Bool.xor key message]) rest tail) := by
  cases key <;> cases message <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, xorCode, state, PairPreparation.operand,
      PairPreparation.fromCells, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append]

theorem run (pastInput pastOutput key message : List Bool) (tail : List (Option Bool))
    (h : key.length = message.length) :
    evalConfigWithin xorCode (state pastInput pastOutput (pairInput key message) tail)
      (8 * key.length + 2) =
      PMF.pure (finish (pastInput ++ pairInput key message) (pastOutput ++ xorList key message) tail) := by
  induction key generalizing pastInput pastOutput message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp h.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, xorCode, state, finish, PairPreparation.operand,
        PairPreparation.fromCells, Instruction.next, Configuration.tape, pairInput, xorList]
  | cons bit keys ih =>
      cases message with
      | nil => simp at h
      | cons m messages =>
          rw [show 8 * (bit :: keys).length + 2 = 8 + (8 * keys.length + 2) by simp; omega,
            pairInput, evalConfigWithin_add, iteration, PMF.pure_bind,
            ih _ _ messages (by simpa using h)]
          simp [xorList, List.append_assoc]

structure Input (width : Nat) where
  key : Bits width
  message : Bits width
  beforeInput : List Bool
  beforeOutput : List Bool
  tail : List (Option Bool)

noncomputable def procedure (width : Nat) : Machine.Procedure (Input width) (Bits width) :=
  Machine.Procedure.ofFixed xorCode
    (fun input => state input.beforeInput input.beforeOutput (pairInput input.key.toList input.message.toList) input.tail)
    (fun input ciphertext => finish
      (input.beforeInput ++ pairInput input.key.toList input.message.toList)
      (input.beforeOutput ++ ciphertext.toList) input.tail)
    (fun input => PMF.pure (Foundation.Symmetric.OneTimePad.encrypt input.key input.message)) (fun _ => 8 * width + 2)
    (fun input => by
      simpa only [Bits.length_toList, Foundation.Symmetric.OneTimePad.encrypt, toList_xor, PMF.pure_map] using
        Prepared.run input.beforeInput input.beforeOutput input.key.toList input.message.toList input.tail (by simp))

theorem interleave_eq (first second : List Bool) :
    PairPreparation.interleave first second = pairInput first second := by
  induction first generalizing second with
  | nil => rfl
  | cons bit first ih => cases second with
    | nil => rfl
    | cons next second => simp only [PairPreparation.interleave, pairInput, ih]

@[simp] theorem finish_output (pastInput pastOutput : List Bool) (tail : List (Option Bool)) :
    (finish pastInput pastOutput tail).outputBits = pastOutput := by
  simp [finish, state, Configuration.outputBits, Tape.bits]

theorem xorList_length (key message : List Bool) (h : key.length = message.length) :
    (xorList key message).length = key.length := by
  induction key generalizing message with
  | nil => simp [xorList]
  | cons bit key ih => cases message with
    | nil => simp at h
    | cons m message => simp [xorList, ih message (by simpa using h)]

/-- List-valued contract accepts every equal-length operand pair. Source
tails are retained by the preparation controller, outside this local code. -/
noncomputable def listProcedure : Machine.Procedure PairPreparation.Input (List Bool) :=
  Machine.Procedure.ofFixed xorCode
    (fun input => { inputTape := PairPreparation.fromCells ((PairPreparation.interleave input.first input.second).map some ++ [none]) })
    (fun input ciphertext => finish (pairInput input.first input.second) ciphertext [])
    (fun input => PMF.pure (xorList input.first input.second)) (fun input => 8 * input.first.length + 2)
    (fun input => by
      have h := Prepared.run [] [] input.first input.second [] input.sameLength
      simpa only [List.nil_append, state, PairPreparation.operand, PairPreparation.fromCells,
        List.reverse_nil, List.map_nil, interleave_eq, PMF.pure_map] using h)

end Machine.OneTimePad.Prepared
