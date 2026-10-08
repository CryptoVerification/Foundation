import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncodedStorage
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorageBackend

/-! Faithful full-code/state bounds for the compiled integrity reduction,
including numerical preparation and header phases. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

def encodedBudget (code : Interactive.Code) (width inputLength count : Nat) : Nat :=
  IntegrityEncoding.bound (compiler.run code).source 0 (inputLength + 1)
    (IntegrityMachine.executionBudget width count) 0 width

theorem compiled_encoded_peak (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (n : Nat) (macKey : TableMAC.Key (width n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ IntegrityMachine.executionBudget (width n) (r.count n))
    (target : IntegrityMachine.Frame Unit)
    (hTarget : target ∈ (IntegrityMachine.eval (compiler.run code).source
      (IntegrityGameCodec.byteSigningOracle macKey) elapsed (IntegrityMachine.initial () (r.input n))).support) :
    ((IntegrityEncoding.complete FiniteBitEncoding.unit).encode
      (IntegrityEncoding.nativePrograms, (compiler.run code).source, target)).length ≤
      encodedBudget code (width n) (r.input n).length (r.count n) := by
  have hOracle : ∀ state ciphertext result,
      result ∈ (IntegrityGameCodec.byteSigningOracle macKey state ciphertext).support →
        (fun _ : Unit => 0) result.1 ≤ (fun _ : Unit => 0) state + 0 ∧ result.2.length ≤ width n := by
    intro state ciphertext result hr
    exact ⟨Nat.le_refl 0, le_of_eq (IntegrityGameCodec.signing_length macKey state ciphertext result hr)⟩
  have hp := IntegrityEncoding.encoded_peak FiniteBitEncoding.unit (fun _ : Unit => 0)
    (by intro state; rfl) (compiler.run code).source (IntegrityGameCodec.byteSigningOracle macKey) 0 (width n) hOracle
    (IntegrityMachine.executionBudget (width n) (r.count n)) elapsed hElapsed
    (IntegrityMachine.initial () (r.input n)) target hTarget
  have ha : IntegrityEncoding.maxScalar (IntegrityMachine.initial () (r.input n)).control = 0 := rfl
  rw [ha] at hp
  exact hp.trans (IntegrityEncoding.bound_mono_initial _ (Nat.le_refl _) (initial_extent (r.input n)) _ _ _)

theorem encodedBudget_polynomial (code : Interactive.Code) {width inputLength count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hInput : PolynomiallyBounded inputLength)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => encodedBudget code (width n) (inputLength n) (count n)) :=
  IntegrityEncoding.bound_polynomial (compiler.run code).source (PolynomiallyBounded.const 0)
    (hInput.add (PolynomiallyBounded.const 1))
    (IntegrityMachine.execution_profile_polynomial hWidth hCount) (PolynomiallyBounded.const 0) hWidth

theorem certificate_encoded_polynomial (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (hInput : PolynomiallyBounded (fun n => (W.resources.input n).length)) :
    PolynomiallyBounded (fun n => encodedBudget W.code (width n)
      (W.resources.input n).length (W.resources.count n)) :=
  encodedBudget_polynomial W.code W.executes.1 hInput W.executes.2.1

theorem certificate_encoded_peak (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (n : Nat) (macKey : TableMAC.Key (width n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ IntegrityMachine.executionBudget (width n) (W.resources.count n))
    (target : IntegrityMachine.Frame Unit)
    (hTarget : target ∈ (IntegrityMachine.eval ((certificate width).mapWitness F A W).code.source
      (IntegrityGameCodec.byteSigningOracle macKey) elapsed
      (IntegrityMachine.initial () (W.resources.input n))).support) :
    ((IntegrityEncoding.complete FiniteBitEncoding.unit).encode
      (IntegrityEncoding.nativePrograms, ((certificate width).mapWitness F A W).code.source, target)).length ≤
      encodedBudget W.code (width n) (W.resources.input n).length (W.resources.count n) :=
  compiled_encoded_peak width W.code W.resources n macKey elapsed hElapsed target hTarget

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
