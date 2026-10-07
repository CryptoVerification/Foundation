import Foundation.Constructions.Symmetric.EncryptThenMAC.Semantics
import Foundation.Constructions.Symmetric.OneTimePadNative
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneUseEncryption

/-! A one-use one-bit pad with an explicit exhaustion state. The native
primitive implements encryption, its updated state, and the failure marker.
The initial key is uniformly random. This is a concrete small-message scheme,
not an implementation of the whole adaptive reduction controller. -/
namespace Foundation.Symmetric.EncryptThenMAC.OneBitEncryption
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

noncomputable def scheme : Encryption where
  Key := fun _ => Bool
  State := fun _ => Bool
  Message := fun _ => Bool
  Ciphertext := fun _ => Bool
  keygen := fun _ => sampleBit
  initial := fun _ => false
  encrypt := fun _ key used message => (true, if used then none else some (Bool.xor key message))
  decrypt := fun _ key ciphertext => some (Bool.xor key ciphertext)
  correctness := by
    intro n key used message ciphertext h
    cases used
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst ciphertext
      cases key <;> cases message <;> rfl
    · simp at h

def oneUseContract : OneUseEncryption scheme where
  exhausted := fun _ => true
  ciphertext := fun _ key message => Bool.xor key message
  first := by intros; rfl
  used := by intros; rfl

namespace Native
open Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def keygenCode : Program := [.randomBit .output, .halt]

/-- The native sampler produces exactly the scheme's one-bit key law. -/
theorem keygen_correct (raw : List Bool) :
    evalWithin keygenCode raw 2 = sampleBit.map (fun bit => some [bit]) := by
  unfold evalWithin
  change (((PMF.pure (Configuration.initial raw)).bind (stepPMF keygenCode)).bind
    (stepPMF keygenCode)).map (fun c => if c.halted then some c.outputBits else none) = _
  rw [PMF.pure_bind]
  have first : stepPMF keygenCode (Configuration.initial raw) =
      sampleBit.map (fun bit => if bit then
        { (Configuration.initial raw) with pc := 1, outputTape := { current := some true } }
      else { (Configuration.initial raw) with pc := 1, outputTape := { current := some false } }) := rfl
  rw [first]
  rw [PMF.bind_map, PMF.map_bind]
  have h (bit : Bool) :
      (stepPMF keygenCode (if bit then
        { (Configuration.initial raw) with pc := 1, outputTape := { current := some true } }
      else { (Configuration.initial raw) with pc := 1, outputTape := { current := some false } })).map
        (fun c => if c.halted then some c.outputBits else none) = PMF.pure (some [bit]) := by
    cases bit <;> simp [stepPMF, next, keygenCode, Instruction.next, Configuration.initial,
      Configuration.outputBits, Tape.bits, PMF.pure_map]
  simp only [Function.comp_def]
  simp_rw [h]
  simpa only [Function.comp_def] using
    PMF.bind_pure_comp (p := sampleBit) (f := fun bit => some [bit])

theorem keygen_halts (raw : List Bool) : HaltsWithin keygenCode raw 2 := by
  apply haltsWithin_of_no_timeout_support
  rw [keygen_correct]
  simp [PMF.mem_support_map_iff]

def keygenProgram : CryptoLogic.BoundedProgram where
  program := keygenCode
  budget := fun _ => 2
  polynomial := PolynomiallyBounded.const 2
  halts := keygen_halts

/-- Packet input is [used, key, message]. Packet output is the new state,
followed by a success bit and, on success, the ciphertext. No whole-packet
operation is treated as a native instruction. -/
def encryptionCode : Program :=
  [.write .output true, .moveRight .output, .branch .input 24 3 21,
   .write .output true, .moveRight .output, .moveRight .input,
   .branch .input 24 7 14,
   .moveRight .input, .branch .input 24 9 11,
   .write .output false, .jump 24, .write .output true, .jump 24, .halt,
   .moveRight .input, .branch .input 24 16 18,
   .write .output true, .jump 24, .write .output false, .jump 24, .halt,
   .write .output false, .jump 24, .halt, .halt]

def output (used key message : Bool) : List Bool :=
  if used then [true, false] else [true, true, Bool.xor key message]

/-- Padded native execution has exactly the prescribed packet law. -/
theorem encryption_correct (used key message : Bool) :
    evalWithin encryptionCode [used, key, message] 12 = PMF.pure (some (output used key message)) := by
  cases used <;> cases key <;> cases message <;>
    simp [evalWithin, evalConfigWithin, stepPMF, next, encryptionCode, output,
      Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
      Configuration.updateTape, Configuration.advance, Configuration.outputBits,
      Tape.write, Tape.moveRight, Tape.bits, PMF.pure_map]

/-- Successful ciphertexts and exhausted-key failures encode the exact
stateful encryption function used by the generic composition theorem. -/
def encodeResponse (response : Bool × Option Bool) : List Bool :=
  response.1 :: (match response.2 with | none => [false] | some bit => [true, bit])

theorem realizes_scheme (n : Nat) (used key message : Bool) :
    evalWithin encryptionCode [used, key, message] 12 =
      PMF.pure (some (encodeResponse (scheme.encrypt n key used message))) := by
  rw [encryption_correct]
  cases used <;> rfl

/-- Every finite packet, including malformed ones, stops within 12 steps. -/
theorem all_halts (raw : List Bool) : HaltsWithin encryptionCode raw 12 := by
  apply haltsWithin_of_no_timeout_support
  cases raw with
  | nil =>
      simp [evalWithin, evalConfigWithin, stepPMF, next, encryptionCode,
        Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Configuration.outputBits,
        Tape.write, Tape.moveRight, Tape.bits, PMF.pure_map]
  | cons used rest =>
      cases used <;> cases rest with
      | nil =>
          simp [evalWithin, evalConfigWithin, stepPMF, next, encryptionCode,
            Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
            Configuration.updateTape, Configuration.advance, Configuration.outputBits,
            Tape.write, Tape.moveRight, Tape.bits, PMF.pure_map]
      | cons key rest =>
          cases key <;> cases rest with
          | nil =>
              simp [evalWithin, evalConfigWithin, stepPMF, next, encryptionCode,
                Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
                Configuration.updateTape, Configuration.advance, Configuration.outputBits,
                Tape.write, Tape.moveRight, Tape.bits, PMF.pure_map]
          | cons message rest =>
              cases message <;>
                simp [evalWithin, evalConfigWithin, stepPMF, next, encryptionCode,
                  Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
                  Configuration.updateTape, Configuration.advance, Configuration.outputBits,
                  Tape.write, Tape.moveRight, Tape.bits, PMF.pure_map]

def encryptionProgram : CryptoLogic.BoundedProgram where
  program := encryptionCode
  budget := fun _ => 12
  polynomial := PolynomiallyBounded.const 12
  halts := all_halts

end Native
end Foundation.Symmetric.EncryptThenMAC.OneBitEncryption
