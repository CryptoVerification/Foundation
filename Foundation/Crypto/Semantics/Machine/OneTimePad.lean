import Foundation.Crypto.Semantics.Machine.FiniteRandomness
import Foundation.Crypto.Semantics.Machine.PolynomialTime
import Foundation.Constructions.Symmetric.OneTimePad

/-! Fixed native bit-level programs for one-time-pad keys, XOR, and fresh
key encryption. Length is input data, not a code-generation parameter.
The fresh encryption program retains its generated secret on the input tape;
only the ciphertext output tape is exposed to the observer. -/
namespace Machine.OneTimePad
open Foundation.Probability Foundation.Symmetric
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

def keygen : Program :=
  [.branch .input 5 1 1, .randomBit .output, .moveRight .input,
   .moveRight .output, .jump 0, .halt]

/-- Input consists of successive key/message pairs. -/
def xorCode : Program :=
  [.branch .input 16 1 7,
   .moveRight .input, .branch .input 16 3 5,
   .write .output false, .jump 13, .write .output true, .jump 13,
   .moveRight .input, .branch .input 16 9 11,
   .write .output true, .jump 13, .write .output false, .jump 13,
   .moveRight .input, .moveRight .output, .jump 0, .halt]

/-- Input is the plaintext. Each consumed cell becomes a fresh key bit.
The finite control remembers the plaintext bit while sampling that cell. -/
def freshCode : Program :=
  [.branch .input 16 1 7,
   .randomBit .input, .branch .input 16 3 5,
   .write .output false, .jump 13, .write .output true, .jump 13,
   .randomBit .input, .branch .input 16 9 11,
   .write .output true, .jump 13, .write .output false, .jump 13,
   .moveRight .input, .moveRight .output, .jump 0, .halt]

def state (pastInput pastOutput remaining : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := pastInput.reverse.map some },
    outputTape := { left := pastOutput.reverse.map some } }

def finish (pc : Nat) (pastInput pastOutput : List Bool) : Configuration :=
  { state pastInput pastOutput [] with pc := pc, halted := true }

@[simp] theorem finish_output (pc : Nat) (pastInput pastOutput : List Bool) :
    (finish pc pastInput pastOutput).outputBits = pastOutput := by
  simp [finish, state, Configuration.outputBits, Tape.bits]

@[simp] theorem state_initial (remaining : List Bool) :
    state [] [] remaining = Configuration.initial remaining := by
  cases remaining <;> rfl

theorem keygen_iteration (pastInput pastKey rest : List Bool) (marker : Bool) :
    evalConfigWithin keygen (state pastInput pastKey (marker :: rest)) 5 =
      sampleBit.map (fun bit => state (pastInput ++ [marker]) (pastKey ++ [bit]) rest) := by
  cases marker <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, keygen, state, Tape.ofBits,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, PMF.bind_map,
      PMF.map_comp, Function.comp_def, List.reverse_append]
  all_goals
    change sampleBit.bind _ = sampleBit.map _
    rw [PMF.map]
    congr 1
    funext bit
    cases bit <;> simp [stepPMF, next, keygen, state, Tape.ofBits, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight, List.reverse_append]

/-- Exact joint tape law of the key-generation program. -/
theorem keygen_run (pastInput pastKey remaining : List Bool) :
    evalConfigWithin keygen (state pastInput pastKey remaining) (5 * remaining.length + 2) =
      (uniform (Bits remaining.length)).map (fun key =>
        finish 5 (pastInput ++ remaining) (pastKey ++ key.toList)) := by
  induction remaining generalizing pastInput pastKey with
  | nil => simp [evalConfigWithin, stepPMF, next, keygen, state, finish,
      Tape.ofBits, Instruction.next, Configuration.tape, Bits.toList,
      PMF.map_const, Function.const_def]
  | cons marker rest ih =>
      rw [show 5 * (marker :: rest).length + 2 = 5 + (5 * rest.length + 2) by simp; omega,
        evalConfigWithin_add, keygen_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      simp only [List.length_cons]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def,
        Bits.toList, List.ofFn_succ, List.append_assoc]

def pairInput : List Bool → List Bool → List Bool
  | key :: keys, message :: messages => key :: message :: pairInput keys messages
  | _, _ => []

def xorList : List Bool → List Bool → List Bool
  | key :: keys, message :: messages => Bool.xor key message :: xorList keys messages
  | _, _ => []

theorem toList_xor {length : Nat} (key message : Bits length) :
    (Bits.xor key message).toList = xorList key.toList message.toList := by
  induction length with
  | zero => simp [Bits.toList, xorList]
  | succ length ih =>
      simp only [Bits.toList, List.ofFn_succ, Bits.xor, xorList]
      exact congrArg (Bool.xor (key 0) (message 0) :: ·)
        (ih (fun i => key i.succ) (fun i => message i.succ))

theorem xor_iteration (pastInput pastOutput rest : List Bool) (key message : Bool) :
    evalConfigWithin xorCode (state pastInput pastOutput (key :: message :: rest)) 8 =
      PMF.pure (state (pastInput ++ [key, message])
        (pastOutput ++ [Bool.xor key message]) rest) := by
  cases key <;> cases message <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, xorCode, state, Tape.ofBits,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append]

theorem xor_run (pastInput pastOutput key message : List Bool)
    (h : key.length = message.length) :
    evalConfigWithin xorCode (state pastInput pastOutput (pairInput key message))
      (8 * key.length + 2) =
      PMF.pure (finish 16 (pastInput ++ pairInput key message)
        (pastOutput ++ xorList key message)) := by
  induction key generalizing pastInput pastOutput message with
  | nil =>
      have hm : message = [] := List.length_eq_zero_iff.mp h.symm
      subst message
      simp [evalConfigWithin, stepPMF, next, xorCode, state, finish,
        Tape.ofBits, Instruction.next, Configuration.tape, pairInput, xorList]
  | cons bit keys ih =>
      cases message with
      | nil => simp at h
      | cons m messages =>
          rw [show 8 * (bit :: keys).length + 2 = 8 + (8 * keys.length + 2) by simp; omega,
            pairInput, evalConfigWithin_add, xor_iteration, PMF.pure_bind,
            ih _ _ messages (by simpa using h)]
          simp [pairInput, xorList, List.append_assoc]

theorem fresh_iteration (pastKey pastCipher rest : List Bool) (message : Bool) :
    evalConfigWithin freshCode (state pastKey pastCipher (message :: rest)) 8 =
      sampleBit.map (fun bit => state (pastKey ++ [bit])
        (pastCipher ++ [Bool.xor bit message]) rest) := by
  cases message <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, freshCode, state, Tape.ofBits,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, PMF.bind_map,
      PMF.map_comp, Function.comp_def, List.reverse_append]
  all_goals
    change sampleBit.bind _ = sampleBit.map _
    rw [PMF.map]
    congr 1
    funext bit
    cases bit <;> simp [stepPMF, next, freshCode, state, Tape.ofBits, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight, List.reverse_append]

/-- The key and ciphertext are jointly realized by the same native run. -/
theorem fresh_run (pastKey pastCipher message : List Bool) :
    evalConfigWithin freshCode (state pastKey pastCipher message) (8 * message.length + 2) =
      (uniform (Bits message.length)).map (fun key =>
        finish 16 (pastKey ++ key.toList) (pastCipher ++ xorList key.toList message)) := by
  induction message generalizing pastKey pastCipher with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, freshCode, state, finish,
        Tape.ofBits, Instruction.next, Configuration.tape, Bits.toList,
        xorList, PMF.map_const, Function.const_def]
  | cons m messages ih =>
      rw [show 8 * (m :: messages).length + 2 = 8 + (8 * messages.length + 2) by simp; omega,
        evalConfigWithin_add, fresh_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      simp only [List.length_cons]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Bits.toList,
        List.ofFn_succ, xorList, List.append_assoc]


/-- Typed-width law avoids any change of random-bit domain by a decoder. -/
theorem keygen_typed_run (width : Nat) (pastInput pastKey : List Bool) :
    evalConfigWithin keygen (state pastInput pastKey (List.replicate width true)) (5 * width + 2) =
      (uniform (Bits width)).map (fun key =>
        finish 5 (pastInput ++ List.replicate width true) (pastKey ++ key.toList)) := by
  induction width generalizing pastInput pastKey with
  | zero =>
      simp [evalConfigWithin, stepPMF, next, keygen, state, finish, Tape.ofBits,
        Instruction.next, Configuration.tape, Bits.toList, PMF.map_const, Function.const_def]
  | succ width ih =>
      rw [List.replicate_succ, show 5 * (width + 1) + 2 = 5 + (5 * width + 2) by omega,
        evalConfigWithin_add, keygen_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Bits.toList,
        List.ofFn_succ, List.replicate_succ, List.append_assoc]

theorem fresh_typed_run {width : Nat} (message : Bits width) (pastKey pastCipher : List Bool) :
    evalConfigWithin freshCode (state pastKey pastCipher message.toList) (8 * width + 2) =
      (uniform (Bits width)).map (fun key => finish 16 (pastKey ++ key.toList)
        (pastCipher ++ (Foundation.Symmetric.OneTimePad.encrypt key message).toList)) := by
  induction width generalizing pastKey pastCipher with
  | zero =>
      simp [evalConfigWithin, stepPMF, next, freshCode, state, finish, Tape.ofBits,
        Instruction.next, Configuration.tape, Bits.toList, PMF.map_const, Function.const_def]
  | succ width ih =>
      conv_lhs => rw [show message.toList =
        (message 0) :: Bits.toList (fun i : Fin width => message i.succ) by
          simp [Bits.toList, List.ofFn_succ]]
      rw [show 8 * (width + 1) + 2 = 8 + (8 * width + 2) by omega,
        evalConfigWithin_add, fresh_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Bits.toList,
        List.ofFn_succ, Foundation.Symmetric.OneTimePad.encrypt, Bits.xor, List.append_assoc]
      congr 1
      funext bit
      congr 1
      funext key
      simp [Bits.xor, Bool.xor_comm]
      rfl

@[simp] theorem finish_halted (pc : Nat) (pastInput pastOutput : List Bool) :
    (finish pc pastInput pastOutput).halted = true := rfl

theorem keygen_output (input : List Bool) :
    evalWithin keygen input (5 * input.length + 2) =
      (uniform (Bits input.length)).map (fun key => some key.toList) := by
  rw [evalWithin, ← state_initial, keygen_run]
  simp [PMF.map_comp, Function.comp_def]

theorem xor_output {length : Nat} (key message : Bits length) :
    evalWithin xorCode (pairInput key.toList message.toList) (8 * length + 2) =
      PMF.pure (some (Foundation.Symmetric.OneTimePad.encrypt key message).toList) := by
  have h := xor_run [] [] key.toList message.toList (by simp)
  simp only [Bits.length_toList] at h
  rw [evalWithin, ← state_initial, h]
  simp [PMF.pure_map, Foundation.Symmetric.OneTimePad.encrypt, toList_xor]

theorem fresh_output {length : Nat} (message : Bits length) :
    evalWithin freshCode message.toList (8 * length + 2) =
      (uniform (Bits length)).map (fun key =>
        some (Foundation.Symmetric.OneTimePad.encrypt key message).toList) := by
  rw [evalWithin, ← state_initial, fresh_typed_run]
  simp only [PMF.map_comp, Function.comp_def, List.nil_append, finish_halted,
    ↓reduceIte, finish_output]

theorem keygen_halts (input : List Bool) : HaltsWithin keygen input (5 * input.length + 2) := by
  apply haltsWithin_of_no_timeout_support
  rw [keygen_output]
  simp [PMF.mem_support_map_iff]

theorem xor_halts {length : Nat} (key message : Bits length) :
    HaltsWithin xorCode (pairInput key.toList message.toList) (8 * length + 2) := by
  apply haltsWithin_of_no_timeout_support
  rw [xor_output]
  simp

theorem fresh_halts (input : List Bool) : HaltsWithin freshCode input (8 * input.length + 2) := by
  apply haltsWithin_of_no_timeout_support
  rw [evalWithin, ← state_initial, fresh_run]
  simp [PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff]

/-- Total parsing semantics on arbitrary packets: an unpaired final bit
is ignored. Cryptographic requests always contain complete pairs. -/
def xorPairs : List Bool → List Bool
  | key :: message :: rest => Bool.xor key message :: xorPairs rest
  | _ => []

theorem xor_all_run (pastInput pastOutput input : List Bool) :
    evalConfigWithin xorCode (state pastInput pastOutput input) (4 * input.length + 4) =
      PMF.pure (finish 16 (pastInput ++ input) (pastOutput ++ xorPairs input)) := by
  induction input using List.twoStepInduction generalizing pastInput pastOutput with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, xorCode, state, finish,
        Tape.ofBits, Instruction.next, Configuration.tape, xorPairs]
  | singleton bit =>
      cases bit <;> simp [evalConfigWithin, stepPMF, next, xorCode, state, finish,
        Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
        Configuration.advance, Tape.moveRight, xorPairs, List.reverse_append]
  | cons_cons key message rest ih =>
      rw [show 4 * (key :: message :: rest).length + 4 = 8 + (4 * rest.length + 4) by simp; omega,
        evalConfigWithin_add, xor_iteration, PMF.pure_bind, ih]
      simp [xorPairs, List.append_assoc]

theorem xor_all_output (input : List Bool) :
    evalWithin xorCode input (4 * input.length + 4) = PMF.pure (some (xorPairs input)) := by
  rw [evalWithin, ← state_initial, xor_all_run]
  simp [PMF.pure_map, finish, state, Tape.ofBits, Configuration.outputBits, Tape.bits]

theorem xor_all_halts (input : List Bool) : HaltsWithin xorCode input (4 * input.length + 4) := by
  apply haltsWithin_of_no_timeout_support
  rw [xor_all_output]
  simp

theorem keygen_time_polynomial : PolynomiallyBounded (fun n => 5 * n + 2) :=
  ((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2)

theorem xor_time_polynomial : PolynomiallyBounded (fun n => 4 * n + 4) :=
  ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4)

theorem fresh_time_polynomial : PolynomiallyBounded (fun n => 8 * n + 2) :=
  ((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2)

@[simp] theorem finish_input (pc : Nat) (pastInput pastOutput : List Bool) :
    (finish pc pastInput pastOutput).inputTape.bits = pastInput := by
  simp [finish, state, Tape.ofBits, Tape.bits]

/-- Joint native generation/encryption followed by the native decryptor.
The next call's canonical packet is an external call argument, not an
instruction that interleaves a whole string at unit cost. -/
theorem roundtrip {length : Nat} (message : Bits length) :
    (evalConfigWithin freshCode (Configuration.initial message.toList) (8 * length + 2)).bind
      (fun encrypted => evalWithin xorCode
        (pairInput encrypted.inputTape.bits encrypted.outputBits) (8 * length + 2)) =
      PMF.pure (some message.toList) := by
  rw [← state_initial, fresh_typed_run, PMF.bind_map]
  simp only [Function.comp_def, List.nil_append, finish_input, finish_output]
  simp only [xor_output, Foundation.Symmetric.OneTimePad.encrypt, Bits.xor_self_cancel]
  change (uniform (Bits length)).bind (fun _ => PMF.pure (some message.toList)) = _
  simp

theorem keygen_polynomialTime : PolynomialTime keygen :=
  ⟨fun n => 5 * n + 2, keygen_time_polynomial, keygen_halts⟩

theorem xor_polynomialTime : PolynomialTime xorCode :=
  ⟨fun n => 4 * n + 4, xor_time_polynomial, xor_all_halts⟩

theorem fresh_polynomialTime : PolynomialTime freshCode :=
  ⟨fun n => 8 * n + 2, fresh_time_polynomial, fresh_halts⟩

theorem pairInput_length (key message : List Bool) (h : key.length = message.length) :
    (pairInput key message).length = 2 * key.length := by
  induction key generalizing message with
  | nil => simp [pairInput]
  | cons bit keys ih =>
      cases message with
      | nil => simp at h
      | cons m messages =>
          simp only [pairInput, List.length_cons, ih messages (by simpa using h)]
          omega

end Machine.OneTimePad
