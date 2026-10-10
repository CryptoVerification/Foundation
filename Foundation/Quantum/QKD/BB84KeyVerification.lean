import Foundation.Quantum.QKD.KeyVerificationLogic
import Foundation.Quantum.QKD.BB84Collision
import Foundation.Quantum.QKD.ReadClassicalState

/-! Fresh-hash verification of the existing real randomized BB84 raw-key
state. This module performs no error correction and makes no secrecy claim;
it supplies an actual-protocol correctness bound with the public tag retained. -/
namespace Foundation.Quantum.QKD.BB84KeyVerification
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def input {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    State (KeyVerification.Input (Finalization.RawKey n) (RawProtocol.PublicRecord n)) e :=
  relabel
    (restrict (readDensity (Randomized.keyState A k minKey tolerance))
      (fun o : RawProtocol.Output n => o.transcript.accepted = true))
    (fun o => ((o.aliceKey,o.bobKey),o.transcript))

def accepted {n tag : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :=
  KeyVerification.accepted (input A k minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) Hashing.rawHash

def aborted {n tag : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :=
  KeyVerification.aborted (input A k minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) Hashing.rawHash

/-- A finite derivation with empty assumptions, using the concrete verified
collision estimate of the optional-position binary-matrix hash. -/
theorem correctness {n tag : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    CommonKey.correctnessError (accepted (tag := tag) A k minKey tolerance) ≤
      1 / Fintype.card (IdealKey.Key tag) := by
  apply KeyVerificationLogic.sound (fun _ => input A k minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n tag)) Hashing.rawHash
    (1 / Fintype.card (IdealKey.Key tag)) (by positivity)
    (fun a b hab => le_of_eq (Collision.raw_collision a b hab))
    (KeyVerificationLogic.proof _ 0)
  intro i
  exact Fin.elim0 i

theorem branch_mass {n tag : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    mass (accepted (tag := tag) A k minKey tolerance) +
      mass (aborted (tag := tag) A k minKey tolerance) = mass (input A k minKey tolerance) :=
  KeyVerification.branch_mass _ _ _

end
end Foundation.Quantum.QKD.BB84KeyVerification
