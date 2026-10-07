import Foundation.Constructions.Symmetric.EncryptThenMAC.Security
import Foundation.Crypto.Logic.Presented.Resources

/-! Honest operational registration: CPU costs are not inferred from the
semantic oracle syntax. A backend must supply execution/realization witnesses
for the exact two finite compiled programs. This interface does not itself
implement the encryption or signing algorithms. -/
namespace Foundation.Symmetric.EncryptThenMAC.Operational

open CryptoLogic.General
universe v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-- A goal-indexed backend makes the intended cryptographic goal explicit.
Its resource and realization propositions remain the backend's own contract. -/
structure Backend (K : CodeSystem) (machine : K.Machine) (P : CryptoGoal) where
  execution : ExecutionInterface.{0, v} K machine P
  adversaries : AdversaryClass P
  represented : ∀ F A, adversaries.admissible F A →
    ∃ code resources, execution.ExecutesWithin F code resources ∧ execution.Realizes F A code resources

abbrev Backend.object {K : CodeSystem} {machine : K.Machine} {P : CryptoGoal}
    (B : Backend.{v} K machine P) : SecurityObject K machine where
  goal := P
  execution := B.execution
  adversaries := B.adversaries
  represented := B.represented

variable {K : CodeSystem} {auth enc mac : K.Machine}
  {E : Encryption} {M : MAC E.Ciphertext}

/-- These are proof obligations, not an existence claim about arbitrary
host-language algorithms. The compiler syntax is given independently. -/
structure Realization (X : Backend.{v} K auth (goal E M))
    (Y : Backend.{v} K enc (encryptionGoal E)) (Z : Backend.{v} K mac (macGoal E M))
    (encryptionCompiler : Compiler K auth enc) (macCompiler : Compiler K auth mac) where
  encryptionWitness : ∀ F A, X.object.Witness F A →
    Y.object.Witness (fun _ => ()) (fun n => privacyReduction E M n (A n).1)
  macWitness : ∀ F A, X.object.Witness F A →
    Z.object.Witness (fun _ => ()) (fun n => integrityReduction E M n (A n).2)
  encryptionCode : ∀ F A W, (encryptionWitness F A W).code = encryptionCompiler.run W.code
  macCode : ∀ F A W, (macWitness F A W).code = macCompiler.run W.code

/-- Register the proved two-assumption inequality once execution obligations
are discharged. Every target witness retains its real resource type. -/
noncomputable def Realization.certificate {X : Backend.{v} K auth (goal E M)}
    {Y : Backend.{v} K enc (encryptionGoal E)} {Z : Backend.{v} K mac (macGoal E M)}
    {cE : Compiler K auth enc} {cM : Compiler K auth mac}
    (R : Realization X Y Z cE cM) : CertifiedBinaryReduction X.object Y.object Z.object where
  left := {
    transform := ⟨fun _ => (), fun {n} _ A => privacyReduction E M n A.1⟩
    compiler := cE
    mapWitness := R.encryptionWitness
    code_eq := R.encryptionCode }
  right := {
    transform := ⟨fun _ => (), fun {n} _ A => integrityReduction E M n A.2⟩
    compiler := cM
    mapWitness := R.macWitness
    code_eq := R.macCode }
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by intro F A n; exact advantage_le E M n (A n)

/-- Real execution representation discharges the semantic source-class
obligations, rather than postulating that every source attack is admissible. -/
theorem Realization.admissibility {X : Backend.{v} K auth (goal E M)}
    {Y : Backend.{v} K enc (encryptionGoal E)} {Z : Backend.{v} K mac (macGoal E M)}
    {cE : Compiler K auth enc} {cM : Compiler K auth mac}
    (R : Realization X Y Z cE cM) (A : AdversaryFamily (goal E M) (fun _ => ()))
    (hA : X.adversaries.admissible (fun _ => ()) A) :
    (sourceClass E M Y.adversaries Z.adversaries).admissible (fun _ => ()) A :=
  ⟨R.certificate.left.admissible (fun _ => ()) A hA,
    R.certificate.right.admissible (fun _ => ()) A hA⟩

/-- Each output resource value really certifies the exact compiled code. -/
theorem Realization.encryption_executes {X : Backend.{v} K auth (goal E M)}
    {Y : Backend.{v} K enc (encryptionGoal E)} {Z : Backend.{v} K mac (macGoal E M)}
    {cE : Compiler K auth enc} {cM : Compiler K auth mac}
    (R : Realization X Y Z cE cM) (F A) (W : X.object.Witness F A) :
    Y.execution.ExecutesWithin (fun _ => ()) (cE.run W.code)
      (R.encryptionWitness F A W).resources := by
  rw [← R.encryptionCode]
  exact (R.encryptionWitness F A W).executes

end Foundation.Symmetric.EncryptThenMAC.Operational
