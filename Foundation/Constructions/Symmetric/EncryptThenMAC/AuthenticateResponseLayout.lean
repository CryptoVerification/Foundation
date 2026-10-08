import Foundation.Constructions.Symmetric.EncryptThenMAC.AuthenticateResponse
import Foundation.Crypto.Semantics.Machine.RetainedOutput

/-! Exact native authentication output layouts, including the head position.
Equivalent private input stores retain identical output tapes. No runtime
normalization or whole-string observation is used to move that output. -/
namespace Foundation.Symmetric.EncryptThenMAC.AuthenticateResponse
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def successFinish {width : Nat} (key : TableMAC.Key width) (ciphertext : Bool) : Configuration :=
  Machine.OneTimePad.finish (preamble.length + TableMAC.Native.signCode.length + 1)
    ([true, ciphertext] ++ Machine.OneTimePad.pairInput key.1.toList key.2.toList)
    ([true, ciphertext] ++ (TableMAC.sign key ciphertext).toList)

theorem success_configuration {width : Nat} (key : TableMAC.Key width) (ciphertext : Bool) :
    evalConfigWithin code (Configuration.initial
      (true :: ciphertext :: Machine.OneTimePad.pairInput key.1.toList key.2.toList))
      (8 * width + 14) = PMF.pure (successFinish key ciphertext) := by
  let start := beforeSign ciphertext (Machine.OneTimePad.pairInput key.1.toList key.2.toList)
  have hRun := TableMAC.Native.sign_from_run key ciphertext [true] [true, ciphertext]
  have hHalts : ∀ finish, PaddedRunsFor TableMAC.Native.signCode start finish (8 * width + 4) →
      finish.halted = true := by
    intro finish h
    have hm := (mem_support_evalConfigWithin_iff _ _ _ _).mpr h
    rw [hRun, PMF.mem_support_pure_iff] at hm
    subst finish
    rfl
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt preamble TableMAC.Native.signCode
    start (by simp [start, beforeSign, Machine.OneTimePad.state, TableMAC.Native.signCode])
    rfl (8 * width + 4) hHalts
  rw [show 8 * width + 14 = 9 + ((8 * width + 4) + 1) by omega,
    evalConfigWithin_add, success_prefix, PMF.pure_bind]
  unfold code
  dsimp only at hCall
  rw [hCall, hRun, PMF.pure_map]
  rfl

def failureFinish (rows : List Bool) : Configuration :=
  { Configuration.initial (false :: rows) with pc := 13, halted := true, outputTape := { current := some false } }

theorem failure_configuration (rows : List Bool) (extra : Nat) :
    evalConfigWithin code (Configuration.initial (false :: rows)) (3 + extra) = PMF.pure (failureFinish rows) := by
  have hPrefix : evalConfigWithin code (Configuration.initial (false :: rows)) 3 = PMF.pure (failureFinish rows) := by
    simp [evalConfigWithin, stepPMF, next, code, preamble, Program.withSubroutine, failureFinish,
      Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
      Configuration.updateTape, Configuration.advance, Tape.write]
  rw [evalConfigWithin_add, hPrefix, PMF.pure_bind]
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [evalConfigWithin, ih, PMF.pure_bind]
      simp [stepPMF, next, failureFinish]

def responseTape {width : Nat} (key : TableMAC.Key width) : Option Bool → Tape
  | none => { current := some false }
  | some bit => { left := ([true, bit] ++ (TableMAC.sign key bit).toList).reverse.map some }

/-- Both successful and failed branches preserve their actual stopping
layouts; the failed branch does not move its head to a final blank. -/
theorem output_layout {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (evalConfigWithin code (Configuration.initial (input key ciphertext)) (8 * width + 14)).map
      (fun final => (final.halted, final.outputTape)) = PMF.pure (true, responseTape key ciphertext) := by
  cases ciphertext with
  | none =>
      simp only [input, List.cons_append, List.nil_append]
      rw [show 8 * width + 14 = 3 + (8 * width + 11) by omega,
        failure_configuration, PMF.pure_map]
      rfl
  | some bit =>
      simp only [input, List.cons_append, List.nil_append]
      rw [success_configuration, PMF.pure_map]
      rfl

/-- Input blank padding affects neither the completion flag nor any part of
the physical output layout, at the original authentication time bound. -/
theorem output_layout_of_equivalent {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool)
    (privateInput : Tape) (hInput : privateInput.Equivalent (Tape.ofBits (input key ciphertext))) :
    (evalConfigWithin code { inputTape := privateInput } (8 * width + 14)).map
      (fun final => (final.halted, final.outputTape)) = PMF.pure (true, responseTape key ciphertext) := by
  have hConfig : ({ inputTape := privateInput } : Configuration).SameOutput
      (Configuration.initial (input key ciphertext)) := ⟨rfl, rfl, hInput, rfl⟩
  rw [evalConfigWithin_map_eq_of_sameOutput code _ _ hConfig _ _
    (fun first second h => by rw [h.2.1, h.2.2.2])]
  exact output_layout key ciphertext

theorem responseTape_bits {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (responseTape key ciphertext).bits =
      encode (ciphertext.map (fun bit => (bit, TableMAC.sign key bit))) := by
  cases ciphertext <;> simp [responseTape, Tape.bits, encode, List.filterMap_map]

end Foundation.Symmetric.EncryptThenMAC.AuthenticateResponse
