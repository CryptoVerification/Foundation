import Foundation.Quantum.TensorExchange
import Foundation.Quantum.QKD.BB84DecisionRaw
import Foundation.Quantum.QKD.BB84RawSource

/-! Basis-independent input from the actual entangled source and arbitrary
finite-Kraus block attack. Transport its factors to Bob/Alice/Eve, and prove
the measured blocks against the existing uniformly weighted preparations. -/
namespace Foundation.Quantum.QKD.BB84PreparedInput
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84OutcomeCoordinates
set_option backward.isDefEq.respectTransparency false

/-- No later basis or test choice occurs in this source and attack input. -/
def unrotated {n : Nat} {e : Space} (A : BlockAttack n e) :=
  (A.amplify (qubits n)).run (BB84Source.entangled n)

def input {n : Nat} {e : Space} (A : BlockAttack n e) : Density (jointSpace n e) :=
  (BasisChannel.channel (TensorExchange.equivalence (qubits n) e (qubits n))).run (unrotated A)

/-- Same source after Alice's delayed basis operation and Bob's basis gate. -/
def bobRotated {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :=
  (((blockBasisChannel n θ).amplify e).amplify (qubits n)).run (BB84Source.state A θ)

theorem common_rotated {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    (((BB84ErrorTransform.basisChannel n θ).amplify e).run (input A)).matrix =
      ((BasisChannel.channel (TensorExchange.equivalence (qubits n) e (qubits n))).run
        (bobRotated A θ)).matrix := by
  exact (TensorExchange.local_operations (qubits n) e (qubits n)
    (blockGate n θ) (blockGate n θ) (blockGate_isometry n θ) (blockGate_isometry n θ)
    (unrotated A).matrix).symm

theorem slice {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (a : (qubits n).Basis) :
    SourceReplacement.slice (bobRotated A θ).matrix a =
      (1/2:ℂ)^n • (((blockBasisChannel n θ).amplify e).run (A.jointState θ (readBits a))).matrix := by
  change SourceReplacement.slice ((((blockBasisChannel n θ).toKraus.amplify e).amplify (qubits n)).apply
    (BB84Source.state A θ).matrix) a = _
  rw [SourceReplacement.amplify_slice, BB84Source.block]
  exact ((blockBasisChannel n θ).toKraus.amplify e).linear.map_smul _ _

/-- The entire measured pair/Eve record, including each retained Eve coherence. -/
theorem measured_block {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (p q : (signalSpace n).Basis) (u v : e.Basis) :
    (FirstRegister.channel (signalSpace n) e).toKraus.apply
      (((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.apply (input A).matrix)
      (Fintype.equivFin (signalSpace n).Basis p,u) (Fintype.equivFin (signalSpace n).Basis q,v) =
      if p = q then (1/2:ℂ)^n *
        (FirstRegister.channel (qubits n) e).toKraus.apply
          (((blockBasisChannel n θ).amplify e).toKraus.apply (A.jointState θ (readBits p.2)).matrix)
          (Fintype.equivFin (qubits n).Basis p.1,u) (Fintype.equivFin (qubits n).Basis p.1,v)
      else 0 := by
  rw [FirstRegister.apply_entry]
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    rw [FirstRegister.apply_entry]
    simp only [ite_true]
    have hc := common_rotated A θ
    change ((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.apply (input A).matrix =
      (BasisChannel.channel (TensorExchange.equivalence (qubits n) e (qubits n))).toKraus.apply
        (bobRotated A θ).matrix at hc
    rw [hc, BasisChannel.apply]
    change (SourceReplacement.slice (bobRotated A θ).matrix p.2) (p.1,u) (p.1,v) = _
    rw [slice]
    rfl
  · simp only [h, ite_false]

end
end Foundation.Quantum.QKD.BB84PreparedInput
