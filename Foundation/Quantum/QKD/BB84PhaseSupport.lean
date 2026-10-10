import Foundation.Quantum.QKD.CoherentSupport
import Foundation.Quantum.QKD.Qubits
import Foundation.Quantum.QKD.PrivacyAmplificationLogic

/-! Exact finite complementary-support certificate for BB84. This does not
infer a phase support from the observed sample: quantum sampling and smoothing
remain separate obligations. The auxiliary vectors may be arbitrary and need
not be orthogonal or independent of the signal. -/
namespace Foundation.Quantum.QKD.PhaseSupport
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

def gate (n : Nat) : Operator (qubits n) := blockGate n (fun _ => .X)

theorem gate_coisometry (n : Nat) : gate n * (gate n).conjTranspose = 1 := by
  rw [gate, blockGate_adjoint, blockGate_square]

theorem hadamard_flat (i j : Fin 2) : hadamard i j * star (hadamard i j) = (1/2:ℂ) := by
  fin_cases i <;> fin_cases j <;> norm_num [hadamard, hadamardCoefficient_square]

theorem gate_flat (n : Nat) (i j : (qubits n).Basis) :
    gate n i j * star (gate n i j) = (((1/2:ℝ)^n:ℝ):ℂ) := by
  induction n with
  | zero => cases i; cases j; norm_num [gate, blockGate, Matrix.one_apply]
  | succ n ih =>
    rcases i with ⟨i,u⟩
    rcases j with ⟨j,w⟩
    change (hadamard i j * gate n u w) * star (hadamard i j * gate n u w) = _
    rw [star_mul]
    calc
      _ = (hadamard i j * star (hadamard i j)) * (gate n u w * star (gate n u w)) := by ring
      _ = _ := by rw [hadamard_flat, ih]; push_cast; ring

theorem gate_symmetric (n : Nat) (i j : (qubits n).Basis) : gate n i j = gate n j i := by
  induction n with
  | zero => cases i; cases j; rfl
  | succ n ih =>
    rcases i with ⟨i,u⟩
    rcases j with ⟨j,w⟩
    change hadamard i j * gate n u w = hadamard j i * gate n w u
    rw [ih u w]
    congr 1
    simp only [hadamard, and_comm]

/-- An actual coherent joint input, not the corresponding incoherent mixture. -/
def inputVector {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ) : (Space.tensor (qubits n) e).Basis → ℂ :=
  fun p => if p.1 ∈ J then v p.1 p.2 else 0

theorem input_normalized {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1) :
    (CoherentSupport.outer (inputVector n J v)).trace = 1 := by
  rw [← hn]
  simp only [CoherentSupport.outer, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
    Pi.star_apply, inputVector, Fintype.sum_prod_type, Matrix.sum_apply]
  rw [Finset.sum_comm]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self]

def input {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1) : Density (.tensor (qubits n) e) where
  matrix := CoherentSupport.outer (inputVector n J v)
  positive := CoherentSupport.outer_positive _
  normalized := input_normalized n J v hn

def state {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1) : Guessing.CQ (qubits n).Basis e :=
  CoherentSupport.measured J (gate n) v (gate_coisometry n) hn

/-- Every conditional auxiliary matrix is obtained by applying the actual
Hadamard channel to the coherent joint state and reading its measured diagonal. -/
theorem physical_block {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1)
    (z : (qubits n).Basis) (u w : e.Basis) :
    (((blockBasisChannel n (fun _ => .X)).amplify e).run (input n J v hn)).matrix
      (z,u) (z,w) = (state n J v hn).block z u w := by
  change ((Kraus.single (gate n)).amplify e).apply _ (z,u) (z,w) = _
  rw [Kraus.amplify_apply_entry]
  simp only [Kraus.single, Fintype.sum_unique, input, inputVector, CoherentSupport.outer,
    Matrix.vecMulVec_apply, Pi.star_apply, state, CoherentSupport.measured,
    CoherentSupport.amplitude, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul, apply_ite star, star_zero]
  simp_rw [gate_symmetric n z]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def bound (n : Nat) (J : Finset (qubits n).Basis) : ℝ := J.card * (1/2:ℝ)^n

theorem bound_nonneg (n : Nat) (J : Finset (qubits n).Basis) : 0 ≤ bound n J := by
  unfold bound
  positivity

theorem dominated {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1) :
    Subnormalized.Dominated (Subnormalized.ofCQ (state n J v hn))
      (CoherentSupport.reference J v hn) (bound n J) :=
  CoherentSupport.measured_dominated J (gate n) v (gate_coisometry n) hn _
    (fun _ _ z => gate_flat n _ z)

theorem guessing {e : Space} (n : Nat) (J : Finset (qubits n).Basis)
    (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1) :
    Subnormalized.probability (Subnormalized.ofCQ (state n J v hn)) ≤ bound n J :=
  Subnormalized.probability_le_dominated _ _ _ (dominated n J v hn)

/-- A concrete derivation in the existing privacy-amplification calculus. Its
operator-domination hypothesis is discharged by complementary support. -/
theorem privacy {e : Space} {Y S : Type} [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    (n : Nat) (J : Finset (qubits n).Basis) (v : (qubits n).Basis → e.Basis → ℂ)
    (hn : (∑ i ∈ J, CoherentSupport.outer (v i)).trace = 1)
    (p : PMF S) (h : S → (qubits n).Basis → Y)
    (hc : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    (PrivacyAmplificationLogic.model p h
      (fun _ => Subnormalized.ofCQ (state n J v hn))
      (fun _ => CoherentSupport.reference J v hn) hc).Carrier
      (.distance 0 ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*(bound n J*1))))) := by
  apply PrivacyAmplificationLogic.sound p h _ _ hc
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0 (bound n J) 1 _
      (bound_nonneg n J) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact dominated n J v hn
  · have hi1 : i = 1 := by omega
    subst i
    exact (Subnormalized.ofCQ (state n J v hn)).bounded

end
end Foundation.Quantum.QKD.PhaseSupport
