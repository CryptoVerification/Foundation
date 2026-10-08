import Foundation.Constructions.Symmetric.PRGResource

namespace Foundation.Symmetric.Examples

open Foundation.Probability Machine
open scoped ENNReal

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- A deliberately insecure test generator: its first output bit is zero.
This is an execution fixture, not an asserted secure PRG. -/
def testGenerator : Generator where
  seedLength _ := 1
  outputLength _ := 2
  generate _ seed i := if i = 0 then false else seed 0

def testMessages : Bits 2 × Bits 2 := (fun _ => false, fun i => i = 0)

def testProgram : Machine.Program :=
  List.replicate 11 (.moveRight .input) ++
    [.branch .input 14 14 12, .write .output true, .halt, .write .output false, .halt]

def testHeader : List Bool := testGenerator.header 0 testMessages

/-- Two distinct emitted programs preserve the supplied attack code. -/
example : Generator.reductionPrograms testProgram =
    (.masked false testProgram, .masked true testProgram) := rfl

/-- info: (some false, 14) -/
#guard_msgs in
#eval
  let code := Masking.Code.native testProgram
  let (finish, used) := Masking.simulate code false 100
    (Masking.initial code testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

/-- info: (some false, 43) -/
#guard_msgs in
#eval
  let code := (Generator.reductionPrograms testProgram).1
  let (finish, used) := Masking.simulate code false 100
    (Masking.initial code testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

/-- info: (some true, 43) -/
#guard_msgs in
#eval
  let code := (Generator.reductionPrograms testProgram).2
  let (finish, used) := Masking.simulate code false 100
    (Masking.initial code testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

/-- info: (none, 42) -/
#guard_msgs in
#eval
  let code := (Generator.reductionPrograms testProgram).2
  let (finish, used) := Masking.simulate code false 42
    (Masking.initial code testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

/-- info: [(false, false), (true, true)] -/
#guard_msgs in
#eval [false, true].map fun bit =>
  let code := Masking.Code.native [.randomBit .output, .halt]
  let (finish, _) := Masking.simulate code bit 2 (Masking.initial code [] [] [] [])
  (bit, (Masking.result finish).getD false)

/-- Kernel-checked result, covering all four two-bit ciphertexts. -/
theorem test_native_output (first second : Bool) :
    Masking.output (.native testProgram)
      (Masking.initial (.native testProgram) testHeader [false, false] [true, false]
        [first, second]) 14 = PMF.pure (some first) := by
  cases first <;> cases second <;>
    simp [Masking.output, Masking.eval, Masking.step, Masking.initial, Masking.Code.program,
      Masking.result, stepPMF, Machine.next, testProgram, testHeader, Generator.header,
      encodeSecurityParameter, frame, testGenerator, testMessages, Bits.toList,
      Machine.Configuration.initial, Instruction.next, Machine.Configuration.tape,
      Machine.Configuration.updateTape, Machine.Configuration.advance,
      Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_map, List.ofFn_succ]

/-- One fewer transition leaves the write complete but the halt unfinished. -/
theorem test_native_timeout (first second : Bool) :
    Masking.output (.native testProgram)
      (Masking.initial (.native testProgram) testHeader [false, false] [true, false]
        [first, second]) 13 = PMF.pure none := by
  cases first <;> cases second <;>
    simp [Masking.output, Masking.eval, Masking.step, Masking.initial, Masking.Code.program,
      Masking.result, stepPMF, Machine.next, testProgram, testHeader, Generator.header,
      encodeSecurityParameter, frame, testGenerator, testMessages, Bits.toList,
      Machine.Configuration.initial, Instruction.next, Machine.Configuration.tape,
      Machine.Configuration.updateTape, Machine.Configuration.advance,
      Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_map, List.ofFn_succ]

/-- Both fresh random branches, proved in PMF semantics for every input. -/
theorem random_eval (input : List Bool) :
    Masking.eval (.native [.randomBit .output, .halt])
      (.running (Machine.Configuration.initial input)) 2 =
    sampleBit.map (fun bit => Masking.Configuration.running
      { inputTape := Tape.ofBits input, outputTape := { current := some bit },
        pc := 1, halted := true }) := by
  rw [Masking.running_eval]
  have first : evalConfigWithin [.randomBit .output, .halt]
      (Machine.Configuration.initial input) 1 = sampleBit.map (fun bit =>
        ({ pc := 1, inputTape := Tape.ofBits input, outputTape := { current := some bit } } : Machine.Configuration)) := by
    simp [evalConfigWithin, stepPMF, Machine.next, Machine.Configuration.initial,
      Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance, Tape.write]
    congr 1
    funext bit
    cases bit <;> rfl
  change (evalConfigWithin [.randomBit .output, .halt] _ 2).map _ = _
  rw [evalConfigWithin, first, PMF.bind_map]
  have last (bit : Bool) : stepPMF [.randomBit .output, .halt]
      { inputTape := Tape.ofBits input, outputTape := { current := some bit }, pc := 1 } =
    PMF.pure { pc := 1, halted := true, inputTape := Tape.ofBits input, outputTape := { current := some bit } } := by
    simp [stepPMF, Machine.next, Instruction.next]
  simp only [Function.comp_def, last]
  change (sampleBit.map (fun bit =>
    ({ pc := 1, halted := true, inputTape := Tape.ofBits input, outputTape := { current := some bit } } :
      Machine.Configuration))).map Masking.Configuration.running = _
  rw [PMF.map_comp]
  rfl

/-- The source resource class is inhabited by a single fixed randomized
native program for every generator and every public message family. -/
noncomputable def randomWitness (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    G.NativeWitness (fun _ => 2) F (fun _ _ => sampleBit) where
  program := [.randomBit .output, .halt]
  halts := by
    intro n challenge finish hFinish
    change finish ∈ (Masking.eval (.native [.randomBit .output, .halt])
      (.running (Machine.Configuration.initial _)) 2).support at hFinish
    rw [random_eval, PMF.mem_support_map_iff] at hFinish
    obtain ⟨bit, _, rfl⟩ := hFinish
    rfl
  realizes := by
    intro n challenge
    unfold Masking.output
    change (Masking.eval (.native [.randomBit .output, .halt])
      (.running (Machine.Configuration.initial _)) 2).map Masking.result = sampleBit.map some
    rw [random_eval, PMF.map_comp]
    rfl

example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    (G.nativeClass (fun _ => 2)).admissible F (fun _ _ => sampleBit) := ⟨randomWitness G F⟩

example (G : Generator) (F : InstanceFamily G.encryptionGoal) (side : Bool) :
    (G.challengeClass (G.reductionTime (fun _ => 2))).admissible F
      (fun n => G.reduce (F n) side (fun _ => sampleBit)) :=
  ⟨G.mapWitness (fun _ => 2) side F _ (randomWitness G F)⟩

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass t) F (fun n => 2 * ε n) :=
  G.resource_secure t F ε h

example : testGenerator.reductionTime (fun _ => 14) 0 = 43 := rfl

/-- Length-zero OTP secrecy is included, without requiring a nonempty string. -/
example (left right : Bits 0) (observer : Bits 0 → ProbComp Bool) :
    (OneTimePad.ciphertext left).bind observer = (OneTimePad.ciphertext right).bind observer :=
  OneTimePad.perfect_secrecy left right observer

end Foundation.Symmetric.Examples
