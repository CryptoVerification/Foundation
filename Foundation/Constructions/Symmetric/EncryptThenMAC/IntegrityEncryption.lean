import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitEncryption

/-! Physical native primitives for the integrity reduction. These laws keep
both tapes and head positions, so a surrounding controller can resume without
replacing halted output with a host-computed bitstring. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityEncryption
open Foundation.Probability Machine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def keyFinish (raw : List Bool) (key : Bool) : Configuration :=
  { pc := 1, inputTape := Tape.ofBits raw, outputTape := { current := some key }, halted := true }

theorem keygen_configuration (raw : List Bool) :
    evalConfigWithin OneBitEncryption.Native.keygenCode (Configuration.initial raw) 2 =
      sampleBit.map (keyFinish raw) := by
  have first : stepPMF OneBitEncryption.Native.keygenCode (Configuration.initial raw) =
      sampleBit.map (fun key => { Configuration.initial raw with
        pc := 1, outputTape := { current := some key } }) := by
    unfold stepPMF next
    simp only [OneBitEncryption.Native.keygenCode, Configuration.initial,
      List.getElem?_cons_zero, Instruction.next, Bool.false_eq_true, if_false]
    congr 1
    funext bit
    cases bit <;> rfl
  rw [show 2 = 1 + 1 by rfl, evalConfigWithin_add]
  simp only [evalConfigWithin, PMF.pure_bind]
  rw [first, PMF.bind_map]
  have last (key : Bool) :
      stepPMF OneBitEncryption.Native.keygenCode
        { Configuration.initial raw with pc := 1, outputTape := { current := some key } } =
          PMF.pure (keyFinish raw key) := by
    simp [stepPMF, next, OneBitEncryption.Native.keygenCode, Instruction.next,
      Configuration.initial, keyFinish]
  simp only [Function.comp_def]
  simp_rw [last]
  simpa only [Function.comp_def] using PMF.bind_pure_comp (keyFinish raw) sampleBit

/-- Success ends on the ciphertext cell; failure ends on its false marker.
The private input tape remains part of the physical configuration. -/
def finish (used key message : Bool) : Configuration :=
  if used then
    { pc := 24, inputTape := Tape.ofBits [true, key, message],
      outputTape := { left := [some true], current := some false }, halted := true }
  else
    { pc := 24, inputTape := { left := [some key, some false], current := some message },
      outputTape := { left := [some true, some true], current := some (Bool.xor key message) }, halted := true }

def steps (used : Bool) : Nat := if used then 6 else 12

theorem encryption_configuration (used key message : Bool) :
    evalConfigWithin OneBitEncryption.Native.encryptionCode
      (Configuration.initial [used, key, message]) (steps used) =
        PMF.pure (finish used key message) := by
  cases used <;> cases key <;> cases message <;>
    simp [evalConfigWithin, stepPMF, next, OneBitEncryption.Native.encryptionCode,
      finish, steps, Configuration.initial, Tape.ofBits, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight]

theorem finish_halted (used key message : Bool) : (finish used key message).halted = true := by
  cases used <;> rfl

/-- A constant-size controller observation: at most two cells on the left
and the current cell. This never traverses the output bitstring. -/
def response (machine : Configuration) : Option Bool :=
  match machine.outputTape.left with
  | some true :: some true :: _ => some (machine.outputTape.current.getD false)
  | _ => none

def ready (machine : Configuration) : Option (Bool × Option Bool) :=
  if machine.halted then some (true, response machine) else none

theorem response_finish (used key message : Bool) :
    response (finish used key message) = if used then none else some (Bool.xor key message) := by
  cases used <;> rfl

theorem ready_finish (n : Nat) (used key message : Bool) :
    ready (finish used key message) = some (OneBitEncryption.scheme.encrypt n key used message) := by
  cases used <;> rfl

theorem finish_packet (used key message : Bool) :
    (finish used key message).outputBits = OneBitEncryption.Native.output used key message := by
  cases used <;> simp [finish, Configuration.outputBits, Tape.bits, OneBitEncryption.Native.output]

theorem steps_le (used : Bool) : steps used ≤ 12 := by cases used <;> decide

end Foundation.Symmetric.EncryptThenMAC.IntegrityEncryption
