import Foundation.Quantum.QKD.PairwisePhaseHash

/-! The complementary key W and Alice's actual measurement X are bijective
when the basis and detailed error record are fixed (Bouman--Fehr, §6, p.21).
This is a classical outcome permutation, not cloning of a quantum state. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84ErrorTransform
set_option backward.isDefEq.respectTransparency false

def alice : (n : Nat) → (Fin n → BB84Basis) → (qubits n).Basis →
    (qubits n).Basis → (qubits n).Basis
  | 0, _, _, _ => ()
  | n+1, θ, (r,rs), (z,zs) =>
    (if θ 0 = .Z then z else bitXor z r,
      alice n (fun i => θ i.succ) rs zs)

theorem alice_involution (n : Nat) (θ : Fin n → BB84Basis)
    (r z : (qubits n).Basis) : alice n θ r (alice n θ r z) = z := by
  induction n with
  | zero => cases z; rfl
  | succ n ih =>
    rcases r with ⟨r,rs⟩
    rcases z with ⟨z,zs⟩
    cases h : θ 0 <;> simp only [alice, h, ite_true, ite_false, reduceCtorEq,
      bitXor_cancel, ih]

def aliceEquiv (n : Nat) (θ : Fin n → BB84Basis) (r : (qubits n).Basis) :
    (qubits n).Basis ≃ (qubits n).Basis where
  toFun := alice n θ r
  invFun := alice n θ r
  left_inv := alice_involution n θ r
  right_inv := alice_involution n θ r

/-- Undoing the actual coherent error transformation recovers Alice's
original outcome at this error/key coordinate. -/
theorem alice_physical (n : Nat) (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) :
    (relabel n θ (split n θ (r,z))).2 = alice n θ r z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases r with ⟨r,rs⟩
    rcases z with ⟨z,zs⟩
    have h := ih (fun i => θ i.succ) rs zs
    cases hθ : θ 0 <;> simp only [split, relabel, alice, hθ, ite_true, ite_false,
      reduceCtorEq, h, bitXor_comm r z]

def alicePairEquiv (n : Nat) (θ : Fin n → BB84Basis) :
    ((qubits n).Basis × (qubits n).Basis) ≃ ((qubits n).Basis × (qubits n).Basis) where
  toFun p := (alice n θ p.2 p.1,p.2)
  invFun p := (alice n θ p.2 p.1,p.2)
  left_inv p := by simp only [alice_involution]
  right_inv p := by simp only [alice_involution]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
