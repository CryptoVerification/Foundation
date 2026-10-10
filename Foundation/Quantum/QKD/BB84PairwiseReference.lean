import Foundation.Quantum.QKD.BB84SiftedGates
import Foundation.Quantum.InstrumentPost

/-! Fixed-reference coordinates for Bouman--Fehr §6, p.21: Bob Z, Alice X.
The remaining basis change acts only on the complementary key coordinates.
All identities retain arbitrary auxiliary systems and joint coherences. -/
namespace Foundation.Quantum.QKD.BB84PairwiseReference
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84SiftingRandomness
set_option backward.isDefEq.respectTransparency false

def referenceGate (n : Nat) : Operator (.tensor (qubits n) (qubits n)) :=
  Op.tensor (Op.ident (qubits n)) (blockGate n (fun _ => .X))

def keyGate {n : Nat} (θ : Fin n → BB84Basis) : Operator (.tensor (qubits n) (qubits n)) :=
  Op.tensor (blockGate n θ) (blockGate n (fun i => opposite (θ i)))

theorem bit_complement_mul (θ : BB84Basis) : bitGate (opposite θ) * hadamard = bitGate θ := by
  cases θ with
  | Z => exact QKD.hadamard_square
  | X => exact Matrix.one_mul _

theorem block_complement_mul (n : Nat) (θ : Fin n → BB84Basis) :
    blockGate n (fun i => opposite (θ i)) * blockGate n (fun _ => .X) = blockGate n θ := by
  induction n with
  | zero => simp [blockGate]
  | succ n ih =>
    simp only [blockGate, Op.tensor, Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul]
    rw [show bitGate .X = hadamard from rfl, bit_complement_mul]
    exact congrArg (Matrix.kronecker (bitGate (θ 0))) (ih (fun i => θ i.succ))

theorem factor {n : Nat} (θ : Fin n → BB84Basis) :
    keyGate θ * referenceGate n = basisGate n θ := by
  unfold keyGate referenceGate basisGate Op.tensor Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul]
  change Matrix.kronecker (blockGate n θ * 1)
    (blockGate n (fun i => opposite (θ i)) * blockGate n (fun _ => .X)) = _
  rw [Matrix.mul_one, block_complement_mul]
  rfl

theorem reference_isometry (n : Nat) :
    (referenceGate n).conjTranspose * referenceGate n = 1 :=
  tensor_isometry _ _ (by simp [Op.ident]) (blockGate_isometry _ _)

theorem key_isometry {n : Nat} (θ : Fin n → BB84Basis) :
    (keyGate θ).conjTranspose * keyGate θ = 1 :=
  tensor_isometry _ _ (blockGate_isometry _ _) (blockGate_isometry _ _)

def referenceChannel (n : Nat) := Channel.ofIsometry (referenceGate n) (reference_isometry n)
def keyChannel {n : Nat} (θ : Fin n → BB84Basis) := Channel.ofIsometry (keyGate θ) (key_isometry θ)

theorem basis_factor {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    ((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.apply ρ =
      ((keyChannel θ).amplify e).toKraus.apply
        (((referenceChannel n).amplify e).toKraus.apply ρ) := by
  change (Kraus.single (Op.tensor (basisGate n θ) (Op.ident e))).apply ρ =
    (Kraus.single (Op.tensor (keyGate θ) (Op.ident e))).apply
      ((Kraus.single (Op.tensor (referenceGate n) (Op.ident e))).apply ρ)
  have h : Op.tensor (keyGate θ) (Op.ident e) * Op.tensor (referenceGate n) (Op.ident e) =
      Op.tensor (basisGate n θ) (Op.ident e) := by
    unfold Op.tensor Matrix.kronecker
    rw [← Matrix.mul_kronecker_mul, factor]
    simp [Op.ident]
  rw [← h]
  simp only [Kraus.single_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A block gate leaves every computational-basis coordinate with a Z choice fixed. -/
theorem block_fixed (n : Nat) (θ : Fin n → BB84Basis) (x y : (qubits n).Basis)
    (h : blockGate n θ x y ≠ 0) (i : Fin n) (hi : θ i = .Z) : readBits x i = readBits y i := by
  rw [BB84SiftedInput.gate_entry] at h
  have hh := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  rw [hi] at hh
  by_contra hn
  exact hh (by simp [bitGate, hn])

/-- The key-side gate has support only inside a single error-measurement fiber. -/
theorem key_support {n : Nat} (θ : Fin n → BB84Basis)
    (p q : (Space.tensor (qubits n) (qubits n)).Basis) (h : keyGate θ p q ≠ 0) :
    errorBits θ p = errorBits θ q := by
  have hh : blockGate n θ p.1 q.1 ≠ 0 ∧
      blockGate n (fun i => opposite (θ i)) p.2 q.2 ≠ 0 := mul_ne_zero_iff.mp h
  funext i
  cases ht : θ i with
  | Z => simpa only [errorBits, ht, ite_true] using block_fixed n θ p.1 q.1 hh.1 i ht
  | X =>
    have hc : opposite (θ i) = .Z := by simp [ht, opposite]
    simpa only [errorBits, ht, reduceCtorEq, ite_false] using
      block_fixed n (fun i => opposite (θ i)) p.2 q.2 hh.2 i hc

end
end Foundation.Quantum.QKD.BB84PairwiseReference
