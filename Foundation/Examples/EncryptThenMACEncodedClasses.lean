import Foundation.Constructions.Symmetric.EncryptThenMAC.ConcreteEncodedSecurity
import Foundation.Examples.EncryptThenMACPrivacyBackend
import Foundation.Examples.EncryptThenMACIntegrityBackend

/-! Inhabited strengthened classes: actual finite halt callers, genuine
private initialization, and both whole-code/state size witness maps. -/
namespace Foundation.Symmetric.EncryptThenMAC.EncodedClassExamples
open CryptoLogic.General CryptoOracle ConcreteOperational

def width (_ : Nat) : Nat := 2

noncomputable def attacker (n : Nat) :=
  (PrivacyGameCodec.attack width n NativeGameExamples.haltCode 1 [],
    IntegrityGameCodec.attack width n IntegrityGameExamples.haltCode 1 [])

noncomputable def originalWitness : (sourceBackend width).object.Witness (fun _ => ()) attacker where
  code := (PrivacyBackendExamples.sourceWitness.code, IntegrityBackendExamples.sourceWitness.code)
  resources := (PrivacyBackendExamples.profile, IntegrityBackendExamples.profile)
  executes := ⟨PrivacyBackendExamples.sourceWitness.executes, IntegrityBackendExamples.sourceWitness.executes⟩
  realizes := ⟨PrivacyBackendExamples.sourceWitness.realizes, IntegrityBackendExamples.sourceWitness.realizes⟩
  admissible := ⟨(PrivacyBackendExamples.sourceWitness.code, IntegrityBackendExamples.sourceWitness.code),
    (PrivacyBackendExamples.profile, IntegrityBackendExamples.profile),
    ⟨PrivacyBackendExamples.sourceWitness.executes, IntegrityBackendExamples.sourceWitness.executes⟩,
    ⟨PrivacyBackendExamples.sourceWitness.realizes, IntegrityBackendExamples.sourceWitness.realizes⟩⟩

noncomputable def inputWitness : (inputObject width).Witness (fun _ => ()) attacker :=
  SecurityObject.attach (inputCertificate width) _ _ originalWitness
    ⟨PolynomiallyBounded.const 0, PolynomiallyBounded.const 0⟩

noncomputable def encryptionWitness := (encodedCertificate width).left.mapWitness _ _ inputWitness
noncomputable def macWitness := (encodedCertificate width).right.mapWitness _ _ inputWitness

theorem encryption_size_certificate : PrivacyBackend.encodedCertificate width
    ((encodedCertificate width).left.transform.mapFamily (fun _ => ()))
    encryptionWitness.code encryptionWitness.resources := encryptionWitness.executes.2

theorem mac_size_certificate : IntegrityBackend.encodedCertificate width
    ((encodedCertificate width).right.transform.mapFamily (fun _ => ()))
    macWitness.code macWitness.resources := macWitness.executes.2

end Foundation.Symmetric.EncryptThenMAC.EncodedClassExamples
