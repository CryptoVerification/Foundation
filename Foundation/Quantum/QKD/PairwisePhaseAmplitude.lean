import Foundation.Quantum.QKD.PairwisePhaseCoordinates

/-! The amplitude of the actual physical key-side operation in reversible
error/key coordinates. Arbitrary entangled auxiliary amplitudes are retained. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

def rotated {n : Nat} {e : Space} (θ : Fin n → BB84Basis)
    (v : (Space.tensor (signal n) e).Basis → ℂ) : (Space.tensor (signal n) e).Basis → ℂ :=
  (Op.tensor (keyGate θ) (Op.ident e)).mulVec v

theorem rotated_amplitude {n : Nat} {e : Space} (θ : Fin n → BB84Basis)
    (v : (Space.tensor (signal n) e).Basis → ℂ)
    (r z : (qubits n).Basis) (u : e.Basis) :
    rotated θ v (split n θ (r,z),u) =
      ∑ w : (qubits n).Basis, PhaseSupport.gate n z w * v (split n θ (r,w),u) := by
  have he : rotated θ v (split n θ (r,z),u) =
      ∑ p : (signal n).Basis, keyGate θ (split n θ (r,z)) p * v (p,u) := by
    simp [rotated, Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
      mul_ite, ite_mul]
  rw [he]
  calc
    _ = ∑ p : (signal n).Basis,
        keyGate θ (split n θ (r,z)) (split n θ p) * v (split n θ p,u) :=
      (Equiv.sum_comp (equivalence n θ)
        (fun p => keyGate θ (split n θ (r,z)) p * v (p,u))).symm
    _ = _ := by
      simp_rw [key_coefficient, split_involution]
      change (∑ p : (qubits n).Basis × (qubits n).Basis,
        (if r = p.1 then (1:ℂ) else 0) * PhaseSupport.gate n z p.2 *
          v (split n θ p,u)) = _
      simp [Fintype.sum_prod_type, ite_mul]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
