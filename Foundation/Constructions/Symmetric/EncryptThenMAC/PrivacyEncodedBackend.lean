import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyEncodedStorage
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorageBackend

/-! Full bit-state resources of the existing certified finite privacy
compiler. Initial input length remains an explicit polynomial requirement. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

def encodedBudget (code : Interactive.Code) (width inputLength count : Nat) : Nat :=
  PrivacyEncoding.bound (compiler.run code).source 0 (2 * width + inputLength + 1)
    (PrivacyMachine.executionBudget width count) 0 2

theorem compiled_encoded_peak (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (n : Nat) (encryptionKey side : Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ PrivacyMachine.executionBudget (width n) (r.count n))
    (target : PrivacyMachine.Frame Bool)
    (hTarget : target ∈ (PrivacyMachine.eval (compiler.run code).source
      (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) elapsed
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n))).support) :
    ((PrivacyEncoding.complete ConfigurationEncoding.bit).encode
      (PrivacyEncoding.nativePrograms, (compiler.run code).source, target)).length ≤
      encodedBudget code (width n) (r.input n).length (r.count n) := by
  have hp := PrivacyEncoding.encoded_peak ConfigurationEncoding.bit (fun _ : Bool => 1)
    (by intro state; rfl) (compiler.run code).source
    (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) 0 2 (byteOracle_bound n encryptionKey side)
    (PrivacyMachine.executionBudget (width n) (r.count n)) elapsed hElapsed
    (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n)) target hTarget
  have ha : PrivacyEncoding.maxPc
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n)).control = 0 := rfl
  rw [ha] at hp
  have he := initial_extent (List.replicate (2 * width n) true) (r.input n)
  simp only [List.length_replicate] at he
  exact hp.trans (PrivacyEncoding.bound_mono_initial _ (Nat.le_refl _) he _ _ _)

theorem encodedBudget_polynomial (code : Interactive.Code) {width inputLength count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hInput : PolynomiallyBounded inputLength)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => encodedBudget code (width n) (inputLength n) (count n)) :=
  PrivacyEncoding.bound_polynomial (compiler.run code).source (PolynomiallyBounded.const 0)
    ((((PolynomiallyBounded.const 2).mul hWidth).add hInput).add (PolynomiallyBounded.const 1))
    (PrivacyMachine.execution_profile_polynomial hWidth hCount)
    (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 2)

theorem certificate_encoded_polynomial (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (hInput : PolynomiallyBounded (fun n => (W.resources.input n).length)) :
    PolynomiallyBounded (fun n => encodedBudget W.code (width n)
      (W.resources.input n).length (W.resources.count n)) :=
  encodedBudget_polynomial W.code W.executes.1 hInput W.executes.2.1

/-- The resource theorem applies to the exact source code emitted by the
existing security certificate, with its original input and execution clock. -/
theorem certificate_encoded_peak (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (n : Nat) (encryptionKey side : Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ PrivacyMachine.executionBudget (width n) (W.resources.count n))
    (target : PrivacyMachine.Frame Bool)
    (hTarget : target ∈ (PrivacyMachine.eval ((certificate width).mapWitness F A W).code.source
      (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) elapsed
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) (W.resources.input n))).support) :
    ((PrivacyEncoding.complete ConfigurationEncoding.bit).encode
      (PrivacyEncoding.nativePrograms, ((certificate width).mapWitness F A W).code.source, target)).length ≤
      encodedBudget W.code (width n) (W.resources.input n).length (W.resources.count n) :=
  compiled_encoded_peak width W.code W.resources n encryptionKey side elapsed hElapsed target hTarget

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
