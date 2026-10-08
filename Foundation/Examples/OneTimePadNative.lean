import Foundation.Constructions.Symmetric.OneTimePadNative
import Foundation.Examples.PRGEncryption

namespace Foundation.Symmetric.OneTimePadExamples
open Foundation.Probability Machine
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Test interpreter uses the existing native transition function. It
returns whole output bytes, the actual transition count and the input tape. -/
def runProgram (program : Program) (input : List Bool) (coin : Bool) (fuel : Nat) :
    Option (List Bool) × Nat × List Bool :=
  let (out, used) := Masking.simulate (.native program) coin fuel
    (.running (Configuration.initial input))
  match out with
  | .running c => (if c.halted then some c.outputBits else none, used, c.inputTape.bits)
  | _ => (none, used, [])

/-- info: [(some [false, false, false], 17, [true, true, true]), (some [true, true, true], 17, [true, true, true])] -/
#guard_msgs in
#eval [false, true].map fun coin =>
  runProgram OneTimePad.Native.keygenCode (List.replicate 3 true) coin 17

/-- info: (some [false, true, true], 26, [true, true, false, true, true, false]) -/
#guard_msgs in
#eval runProgram OneTimePad.Native.encryptionCode
  (Machine.OneTimePad.pairInput [true, false, true] [true, true, false]) false 26

/-- info: (some [true, true, false], 26, [true, false, false, true, true, true]) -/
#guard_msgs in
#eval runProgram OneTimePad.Native.decryptionCode
  (Machine.OneTimePad.pairInput [true, false, true] [false, true, true]) false 26

/-- info: [(some [false, true, false], 26, [false, false, false]), (some [true, false, true], 26, [true, true, true])] -/
#guard_msgs in
#eval [false, true].map fun coin =>
  runProgram OneTimePad.Native.freshEncryptionCode [false, true, false] coin 26

/-- info: (none, 25, [true, true, true]) -/
#guard_msgs in
#eval runProgram OneTimePad.Native.freshEncryptionCode [false, true, false] true 25

/-- info: [(some [], 2, []), (some [], 2, []), (some [], 2, [])] -/
#guard_msgs in
#eval [OneTimePad.Native.keygenCode, OneTimePad.Native.encryptionCode,
  OneTimePad.Native.freshEncryptionCode].map fun p => runProgram p [] false 2

/-- info: true -/
#guard_msgs in
#eval [OneTimePad.Native.keygenCode, OneTimePad.Native.encryptionCode,
  OneTimePad.Native.freshEncryptionCode].all fun p =>
    match Encodable.decode (α := Program) (Encodable.encode p) with
    | some decoded => decoded == p
    | none => false

example {length : Nat} (message : Bits length) :
    (evalConfigWithin OneTimePad.Native.freshEncryptionCode
      (Configuration.initial message.toList) (8 * length + 2)).bind
        (fun encrypted => evalWithin OneTimePad.Native.decryptionCode
          (Machine.OneTimePad.pairInput encrypted.inputTape.bits encrypted.outputBits)
          (8 * length + 2)) = PMF.pure (some message.toList) :=
  Machine.OneTimePad.roundtrip message

example (length : Nat → Nat) (n : Nat)
    (messages : (OneTimePad.Native.goal length).Instance n)
    (observer : (OneTimePad.Native.goal length).Adversary n messages) :
    (OneTimePad.Native.goal length).advantage n messages observer = 0 :=
  OneTimePad.Native.advantage_zero length n messages observer

/-- A genuinely represented fixed native observer, for every width and
public message pair family. Security is not vacuous for the native class. -/
noncomputable def witness (length : Nat → Nat)
    (F : InstanceFamily (OneTimePad.Native.generator length).encryptionGoal) :
    (OneTimePad.Native.generator length).NativeWitness (fun _ => 2) F (fun _ _ => sampleBit) :=
  Examples.randomWitness _ F

example (length : Nat → Nat)
    (F : InstanceFamily (OneTimePad.Native.generator length).encryptionGoal) :
    BoundedByOnWithin (OneTimePad.Native.generator length).encryptionGoal
      ((OneTimePad.Native.generator length).nativeClass (fun _ => 2)) F (fun _ => 0) :=
  OneTimePad.Native.logic_bounded length (fun _ => 2) F

example (length : Nat → Nat)
    (F : InstanceFamily (OneTimePad.Native.generator length).encryptionGoal) :
    ((Generator.Logic.sharedDerivation (OneTimePad.Native.generator length) (fun _ => 2) F).runWitnesses (fun _ _ => sampleBit)
        (CryptoLogic.General.Backends.PRG.nativeWitness (witness length F))).map
          CryptoLogic.General.CertifiedOutput.emitted =
      [(0, ⟨CryptoLogic.General.Backends.Kind.masking,
        .masked false [.randomBit .output, .halt]⟩),
       (0, ⟨CryptoLogic.General.Backends.Kind.masking,
        .masked true [.randomBit .output, .halt]⟩)] := by
  rw [CryptoLogic.General.Derivation.runWitnesses_emitted]
  exact Generator.Logic.shared_run _ _ _ _

/-- Two encryptions with a reused one-bit key are perfectly distinguishable:
compare an encryption of zero with the challenge ciphertext. -/
theorem reused_key_attack :
    (uniform (Bits 1)).map (fun key =>
      (OneTimePad.encrypt key (fun _ => false)) 0 ==
        (OneTimePad.encrypt key (fun _ => false)) 0) = PMF.pure true ∧
    (uniform (Bits 1)).map (fun key =>
      (OneTimePad.encrypt key (fun _ => false)) 0 ==
        (OneTimePad.encrypt key (fun _ => true)) 0) = PMF.pure false := by
  constructor
  · simp [PMF.map_const, Function.const_def]
  · have h : (fun key : Bits 1 => (OneTimePad.encrypt key (fun _ => false)) 0 ==
        (OneTimePad.encrypt key (fun _ => true)) 0) = fun _ => false := by
      funext key
      simp only [OneTimePad.encrypt, Bits.xor]
      cases key 0 <;> rfl
    rw [h]
    simp [PMF.map_const, Function.const_def]

example (input : List Bool) :
    HaltsWithin OneTimePad.Native.encryptionProgram.program input
      (OneTimePad.Native.encryptionProgram.budget input.length) :=
  OneTimePad.Native.encryptionProgram.halts input

example (input : List Bool) :
    HaltsWithin OneTimePad.Native.freshEncryptionProgram.program input
      (OneTimePad.Native.freshEncryptionProgram.budget input.length) :=
  OneTimePad.Native.freshEncryptionProgram.halts input

/-- An actual finite observer reads the first ciphertext bit. Unlike the
random observer, this observer's output depends on the ciphertext. -/
def firstBitCode : Program :=
  [.branch .input 1 1 3, .write .output false, .halt, .write .output true, .halt]

theorem firstBit_output (input : List Bool) :
    evalWithin firstBitCode input 3 = PMF.pure (some [input.headD false]) := by
  cases input with
  | nil => simp [evalWithin, evalConfigWithin, stepPMF, next, firstBitCode,
      Configuration.initial, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.ofBits, Tape.write, Configuration.outputBits, Tape.bits,
      PMF.pure_map]
  | cons bit rest =>
      cases bit <;> simp [evalWithin, evalConfigWithin, stepPMF, next, firstBitCode,
        Configuration.initial, Instruction.next, Configuration.tape, Configuration.updateTape,
        Configuration.advance, Tape.ofBits, Tape.write, Configuration.outputBits, Tape.bits,
      PMF.pure_map]

noncomputable def firstBitObserver (cipher : Option (List Bool)) : ProbComp Bool :=
  (evalWithin firstBitCode (cipher.getD []) 3).map (fun out => (out.getD []).headD false)

example (left right : Bits 3) :
    (OneTimePad.Native.goal (fun _ => 3)).advantage 0 (left, right) firstBitObserver = 0 :=
  OneTimePad.Native.advantage_zero (fun _ => 3) 0 (left, right) firstBitObserver

end Foundation.Symmetric.OneTimePadExamples
