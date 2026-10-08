import Foundation.Constructions.Symmetric.EncryptThenMAC.ConcreteOperational
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyEncodedSecurity
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncodedSecurity

/-! Both native branches of the authenticated-encryption reduction now
carry polynomial full-code/state size certificates through the common rule. -/
namespace Foundation.Symmetric.EncryptThenMAC.ConcreteOperational
open Machine Foundation.Probability CryptoOracle CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def inputCertificate (width : Nat → Nat) : (sourceBackend width).object.Certificate :=
  fun _ _ r => PolynomiallyBounded (fun n => (r.1.input n).length) ∧
    PolynomiallyBounded (fun n => (r.2.input n).length)

noncomputable def inputObject (width : Nat → Nat) :=
  (sourceBackend width).object.refine (inputCertificate width)
noncomputable def encodedEncryptionObject (width : Nat → Nat) :=
  (encryptionBackend width).object.refine (PrivacyBackend.encodedCertificate width)
noncomputable def encodedMacObject (width : Nat → Nat) :=
  (macBackend width).object.refine (IntegrityBackend.encodedCertificate width)

noncomputable def encodedCertificate (width : Nat → Nat) :
    CertifiedBinaryReduction (inputObject width) (encodedEncryptionObject width) (encodedMacObject width) :=
  (certificate width).refine (inputCertificate width)
    (PrivacyBackend.encodedCertificate width) (IntegrityBackend.encodedCertificate width)
    (by
      intro F A W hInput
      refine ⟨(fun n => PrivacyBackend.encodedBudget W.code.1 (width n)
        (W.resources.1.input n).length (W.resources.1.count n)),
        PrivacyBackend.encodedBudget_polynomial W.code.1 W.executes.1.1 hInput.1 W.executes.1.2.1, ?_⟩
      intro n key side elapsed hElapsed target hTarget
      exact PrivacyBackend.compiled_encoded_peak width W.code.1 W.resources.1
        n key side elapsed hElapsed target hTarget)
    (by
      intro F A W hInput
      refine ⟨(fun n => IntegrityBackend.encodedBudget W.code.2 (width n)
        (W.resources.2.input n).length (W.resources.2.count n)),
        IntegrityBackend.encodedBudget_polynomial W.code.2 W.executes.2.1 hInput.2 W.executes.2.2.1, ?_⟩
      intro n key elapsed hElapsed target hTarget
      exact IntegrityBackend.compiled_encoded_peak width W.code.2 W.resources.2
        n key elapsed hElapsed target hTarget)

@[simp] theorem encoded_encryption_compiler (width : Nat → Nat) :
    (encodedCertificate width).left.compiler = encryptionCompiler := rfl

@[simp] theorem encoded_mac_compiler (width : Nat → Nat) :
    (encodedCertificate width).right.compiler = macCompiler := rfl

@[simp] theorem encoded_losses (width : Nat → Nat) :
    (encodedCertificate width).leftLoss = (certificate width).leftLoss ∧
    (encodedCertificate width).rightLoss = (certificate width).rightLoss := ⟨rfl, rfl⟩

theorem encoded_secure (width : Nat → Nat) (F)
    (hEncryption : (encodedEncryptionObject width).Secure ((certificate width).left.transform.mapFamily F))
    (hMac : (encodedMacObject width).Secure ((certificate width).right.transform.mapFamily F)) :
    (inputObject width).Secure F :=
  (encodedCertificate width).secure F hEncryption hMac

theorem encoded_bounded (width : Nat → Nat) (F) (encryptionEpsilon macEpsilon : Nat → ℝ≥0∞)
    (hEncryption : (encodedEncryptionObject width).Bounded
      ((certificate width).left.transform.mapFamily F) encryptionEpsilon)
    (hMac : (encodedMacObject width).Bounded ((certificate width).right.transform.mapFamily F) macEpsilon) :
    (inputObject width).Bounded F (fun n => encryptionEpsilon n + macEpsilon n) :=
  (encodedCertificate width).bounded F encryptionEpsilon macEpsilon hEncryption hMac

end Foundation.Symmetric.EncryptThenMAC.ConcreteOperational
