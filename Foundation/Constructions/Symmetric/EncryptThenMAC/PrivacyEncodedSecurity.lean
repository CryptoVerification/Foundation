import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyEncodedBackend
import Foundation.Crypto.Logic.General.ExecutionRefinement
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! The privacy reduction maps polynomial-input witnesses into the actual
represented class with polynomial whole-code/state bit bounds. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
open Machine Foundation.Probability CryptoOracle CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def inputCertificate (width : Nat → Nat) : (sourceObject width).Certificate :=
  fun _ _ r => PolynomiallyBounded (fun n => (r.input n).length)

def encodedCertificate (width : Nat → Nat) : (targetObject width).Certificate :=
  fun _ code r => ∃ bits : Nat → Nat, PolynomiallyBounded bits ∧
    ∀ n (encryptionKey side : Bool) elapsed, elapsed ≤ PrivacyMachine.executionBudget (width n) (r.count n) →
      ∀ target ∈ (PrivacyMachine.eval code.source (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side)
        elapsed (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n))).support,
        ((PrivacyEncoding.complete ConfigurationEncoding.bit).encode
          (PrivacyEncoding.nativePrograms, code.source, target)).length ≤ bits n

noncomputable def inputObject (width : Nat → Nat) := (sourceObject width).refine (inputCertificate width)
noncomputable def encodedObject (width : Nat → Nat) := (targetObject width).refine (encodedCertificate width)

noncomputable def encodedReduction (width : Nat → Nat) :
    CertifiedReduction (inputObject width) (encodedObject width) :=
  (certifiedReduction width).refine (inputCertificate width) (encodedCertificate width) (by
    intro F A W hInput
    refine ⟨(fun n => encodedBudget W.code (width n) (W.resources.input n).length (W.resources.count n)),
      certificate_encoded_polynomial width F A W hInput, ?_⟩
    intro n key side elapsed hElapsed target hTarget
    exact certificate_encoded_peak width F A W n key side elapsed hElapsed target hTarget)

@[simp] theorem encodedReduction_compiler (width : Nat → Nat) :
    (encodedReduction width).compiler = compiler := rfl

@[simp] theorem encodedReduction_loss (width : Nat → Nat) :
    (encodedReduction width).reduction.loss = (reduction width).loss := rfl

/-- Target security is required only for the strengthened represented class.
The source retains its genuine execution and adds polynomial input length. -/
theorem encoded_secure (width : Nat → Nat) (F : InstanceFamily (privacyGoal width))
    (h : (encodedObject width).Secure ((reduction width).mapFamily F)) :
    (inputObject width).Secure F :=
  (encodedReduction width).secure F h

theorem encoded_bound (width : Nat → Nat) (F : InstanceFamily (privacyGoal width))
    (epsilon : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin (encodedObject width).goal (encodedObject width).adversaries
      ((reduction width).mapFamily F) epsilon) :
    BoundedByOnWithin (inputObject width).goal (inputObject width).adversaries F epsilon :=
  (encodedReduction width).bounded F epsilon h

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
