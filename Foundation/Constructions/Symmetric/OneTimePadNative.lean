import Foundation.Crypto.Semantics.Machine.OneTimePad
import Foundation.Constructions.Symmetric.PRGLogic

/-! A complete one-time pad: native key generation, native encryption and
decryption, a native generation/encryption experiment, and unconditional zero
advantage. The identity generator registers this concrete construction in the
existing binary logic; the two zero-loss premises are proved, not assumed. -/
namespace Foundation.Symmetric.OneTimePad.Native
open Foundation.Probability
open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Identity on a full-length key, not a stretching generator. -/
def generator (length : Nat → Nat) : Generator where
  seedLength := length
  outputLength := length
  generate := fun _ key => key

def keygenCode : Machine.Program := Machine.OneTimePad.keygen
def encryptionCode : Machine.Program := Machine.OneTimePad.xorCode
def decryptionCode : Machine.Program := Machine.OneTimePad.xorCode
def freshEncryptionCode : Machine.Program := Machine.OneTimePad.freshCode

noncomputable def ciphertext {width : Nat} (message : Bits width) : ProbComp (Option (List Bool)) :=
  Machine.evalWithin freshEncryptionCode message.toList (8 * width + 2)

theorem ciphertext_eq_encrypt {width : Nat} (message : Bits width) :
    ciphertext message = (uniform (Bits width)).map (fun key => some (encrypt key message).toList) :=
  Machine.OneTimePad.fresh_output message

theorem ciphertext_uniform {width : Nat} (message : Bits width) :
    ciphertext message = (uniform (Bits width)).map (fun bits => some bits.toList) := by
  have h := congrArg (fun p => p.map (fun bits : Bits width => some bits.toList))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simp only [Foundation.Symmetric.OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] at h
  exact (ciphertext_eq_encrypt message).trans h

/-- Every probabilistic observer of the actual native output has the same
law in both one-time worlds, with no computational hardness hypothesis. -/
theorem perfect_secrecy {width : Nat} (left right : Bits width)
    (observer : Option (List Bool) → ProbComp Bool) :
    (ciphertext left).bind observer = (ciphertext right).bind observer := by
  rw [ciphertext_uniform, ciphertext_uniform]

/-- The security goal is defined from native executions, not ideal ciphertexts. -/
noncomputable def goal (length : Nat → Nat) : CryptoGoal where
  Instance := fun n => Bits (length n) × Bits (length n)
  Adversary := fun _ _ => Option (List Bool) → ProbComp Bool
  advantage := fun _ messages observer => probabilityGap
    (eventProb ((ciphertext messages.1).bind observer) (· = true))
    (eventProb ((ciphertext messages.2).bind observer) (· = true))

theorem advantage_zero (length : Nat → Nat) (n : Nat) (messages : (goal length).Instance n)
    (observer : (goal length).Adversary n messages) :
    (goal length).advantage n messages observer = 0 := by
  change probabilityGap _ _ = 0
  rw [perfect_secrecy messages.1 messages.2 observer]
  simp [probabilityGap]

theorem bounded (length : Nat → Nat) : BoundedBy (goal length) (fun _ => 0) := by
  intro n messages observer
  rw [advantage_zero]

theorem secure (length : Nat → Nat) (C : AdversaryClass (goal length))
    (F : InstanceFamily (goal length)) : SecureOnWithin (goal length) C F :=
  SecureOnWithin.of_boundedByOn ((bounded length).on F) Negligible.zero C

/-- Native ciphertext bytes coincide with the typed construction used by
registered resource-certified reductions. -/
theorem ciphertext_eq_registered (length : Nat → Nat) (n : Nat) (message : Bits (length n)) :
    ciphertext message = ((generator length).ciphertext n message).map
      (fun bits => some bits.toList) := by
  rw [ciphertext_eq_encrypt, Generator.ciphertext_eq_encrypt, PMF.map_comp]
  rfl

theorem generator_advantage_zero (length : Nat → Nat) (n : Nat)
    (messages : (generator length).Messages n) (observer : (generator length).Observer n) :
    (generator length).prgGoal.advantage n messages observer = 0 := by
  simp [Generator.prgGoal, Generator.real, Generator.ideal, generator,
    Function.comp_def, probabilityGap]

/-- Discharge the existing logic's premise with an exact distributional
identity. No PRG security assumption is introduced for the identity map. -/
theorem premise_bounded (length time : Nat → Nat)
    (F : InstanceFamily (generator length).encryptionGoal) :
    BoundedByOnWithin (generator length).prgGoal
      ((generator length).challengeClass ((generator length).reductionTime time)) F (fun _ => 0) := by
  intro A _ n
  change (generator length).prgGoal.advantage n (F n) (A n) ≤ 0
  rw [generator_advantage_zero]

/-- Zero advantage obtained through the actual registered binary derivation. -/
theorem logic_bounded (length time : Nat → Nat)
    (F : InstanceFamily (generator length).encryptionGoal) :
    BoundedByOnWithin (generator length).encryptionGoal
      ((generator length).nativeClass time) F (fun _ => 0) := by
  have h := Generator.Logic.bounded_twice (generator length) time F (fun _ => 0)
    (premise_bounded length time F)
  simpa using h

theorem logic_secure (length time : Nat → Nat)
    (F : InstanceFamily (generator length).encryptionGoal) :
    SecureOnWithin (generator length).encryptionGoal ((generator length).nativeClass time) F :=
  SecureOnWithin.of_boundedBy (logic_bounded length time F) Negligible.zero

/-- Exact native key distribution on the canonical public unary width. -/
theorem keygen_uniform (width : Nat) :
    Machine.evalWithin keygenCode (List.replicate width true) (5 * width + 2) =
      (uniform (Bits width)).map (fun key => some key.toList) := by
  change Machine.evalWithin Machine.OneTimePad.keygen _ _ = _
  rw [Machine.evalWithin, ← Machine.OneTimePad.state_initial,
    Machine.OneTimePad.keygen_typed_run]
  simp [PMF.map_comp, Function.comp_def]

theorem encryption_correct {width : Nat} (key message : Bits width) :
    Machine.evalWithin encryptionCode (Machine.OneTimePad.pairInput key.toList message.toList)
      (8 * width + 2) = PMF.pure (some (encrypt key message).toList) :=
  Machine.OneTimePad.xor_output key message

theorem decryption_correct {width : Nat} (key cipher : Bits width) :
    Machine.evalWithin decryptionCode (Machine.OneTimePad.pairInput key.toList cipher.toList)
      (8 * width + 2) = PMF.pure (some (decrypt key cipher).toList) :=
  Machine.OneTimePad.xor_output key cipher

theorem profile_time_polynomial {length : Nat → Nat} (h : PolynomiallyBounded length) :
    PolynomiallyBounded (fun n => 5 * length n + 2) ∧
    PolynomiallyBounded (fun n => 8 * length n + 2) :=
  ⟨((PolynomiallyBounded.const 5).mul h).add (PolynomiallyBounded.const 2),
   ((PolynomiallyBounded.const 8).mul h).add (PolynomiallyBounded.const 2)⟩

/-- Reusing one pad exposes the plaintext XOR. This marks the scope of the
one-time theorem with a kernel-checked algebraic counterexample invariant. -/
theorem reused_key_reveals_xor {width : Nat} (key left right : Bits width) :
    Bits.xor (encrypt key left) (encrypt key right) = Bits.xor left right := by
  funext i
  simp only [Bits.xor, encrypt]
  cases key i <;> cases left i <;> cases right i <;> rfl

/-- Ready-to-use certificates in the existing finite-program framework. -/
def keygenProgram : CryptoLogic.BoundedProgram where
  program := keygenCode
  budget := fun n => 5 * n + 2
  polynomial := Machine.OneTimePad.keygen_time_polynomial
  halts := Machine.OneTimePad.keygen_halts

def encryptionProgram : CryptoLogic.BoundedProgram where
  program := encryptionCode
  budget := fun n => 4 * n + 4
  polynomial := Machine.OneTimePad.xor_time_polynomial
  halts := Machine.OneTimePad.xor_all_halts

def decryptionProgram : CryptoLogic.BoundedProgram := encryptionProgram

def freshEncryptionProgram : CryptoLogic.BoundedProgram where
  program := freshEncryptionCode
  budget := fun n => 8 * n + 2
  polynomial := Machine.OneTimePad.fresh_time_polynomial
  halts := Machine.OneTimePad.fresh_halts

@[simp] theorem encryption_input_length {width : Nat} (key message : Bits width) :
    (Machine.OneTimePad.pairInput key.toList message.toList).length = 2 * width := by
  rw [Machine.OneTimePad.pairInput_length _ _ (by simp)]
  simp

end Foundation.Symmetric.OneTimePad.Native
