import Foundation.Quantum.QKD.BB84PreparedInput
import Foundation.Quantum.QKD.BB84SiftedGates

/-! The actual attacked entangled source with independent Alice/Bob bases.
The full Eve blocks are retained; no independent-signal attack is assumed. -/
namespace Foundation.Quantum.QKD.BB84MixedPreparedInput
noncomputable section
open BB84PreparedInput BB84ErrorTransform BB84DelayedMeasurements BB84OutcomeCoordinates
set_option backward.isDefEq.respectTransparency false

/-- Independent Alice and Bob basis choices, including mismatched positions. -/
def bobRotated {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis) :=
  (((blockBasisChannel n bob).amplify e).amplify (qubits n)).run (BB84Source.state A alice)

theorem rotated {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis) :
    ((BB84SiftedInput.fullChannel bob alice e).run (input A)).matrix =
      ((BasisChannel.channel (TensorExchange.equivalence (qubits n) e (qubits n))).run
        (bobRotated A alice bob)).matrix := by
  exact (TensorExchange.local_operations (qubits n) e (qubits n)
    (blockGate n bob) (blockGate n alice) (blockGate_isometry n bob) (blockGate_isometry n alice)
    (unrotated A).matrix).symm

theorem slice {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (a : (qubits n).Basis) :
    SourceReplacement.slice (bobRotated A alice bob).matrix a =
      (1/2:ℂ)^n • (((blockBasisChannel n bob).amplify e).run (A.jointState alice (readBits a))).matrix := by
  change SourceReplacement.slice ((((blockBasisChannel n bob).toKraus.amplify e).amplify (qubits n)).apply
    (BB84Source.state A alice).matrix) a = _
  rw [SourceReplacement.amplify_slice, BB84Source.block]
  exact ((blockBasisChannel n bob).toKraus.amplify e).linear.map_smul _ _

/-- The entire measured pair/Eve record, including each retained Eve coherence. -/
theorem measured_block {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (p q : (signalSpace n).Basis) (u v : e.Basis) :
    (FirstRegister.channel (signalSpace n) e).toKraus.apply
      ((BB84SiftedInput.fullChannel bob alice e).toKraus.apply (input A).matrix)
      (Fintype.equivFin (signalSpace n).Basis p,u) (Fintype.equivFin (signalSpace n).Basis q,v) =
      if p = q then (1/2:ℂ)^n *
        (FirstRegister.channel (qubits n) e).toKraus.apply
          (((blockBasisChannel n bob).amplify e).toKraus.apply (A.jointState alice (readBits p.2)).matrix)
          (Fintype.equivFin (qubits n).Basis p.1,u) (Fintype.equivFin (qubits n).Basis p.1,v)
      else 0 := by
  rw [FirstRegister.apply_entry]
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    rw [FirstRegister.apply_entry]
    simp only [ite_true]
    have hc := rotated A alice bob
    change (BB84SiftedInput.fullChannel bob alice e).toKraus.apply (input A).matrix =
      (BasisChannel.channel (TensorExchange.equivalence (qubits n) e (qubits n))).toKraus.apply
        (bobRotated A alice bob).matrix at hc
    rw [hc, BasisChannel.apply]
    change (SourceReplacement.slice (bobRotated A alice bob).matrix p.2) (p.1,u) (p.1,v) = _
    rw [slice]
    rfl
  · simp only [h, ite_false]


end
end Foundation.Quantum.QKD.BB84MixedPreparedInput
