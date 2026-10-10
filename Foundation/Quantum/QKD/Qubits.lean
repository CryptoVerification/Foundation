import Foundation.Quantum.QKD.BB84Basis
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite BB84 signal blocks. Computational basis indices are explicitly
equivalent to bit strings, not an assumption that quantum states factor. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

def qubits : Nat → Space
  | 0 => .unit
  | n+1 => .tensor .bit (qubits n)

def readBits : {n : Nat} → (qubits n).Basis → Fin n → Fin 2
  | 0, _ => Fin.elim0
  | _+1, (b,r) => Fin.cases b (readBits r)

def writeBits : (n : Nat) → (Fin n → Fin 2) → (qubits n).Basis
  | 0, _ => ()
  | n+1, b => (b 0, writeBits n (fun i => b i.succ))

theorem read_write (n : Nat) (b : Fin n → Fin 2) : readBits (writeBits n b) = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [readBits, writeBits, Fin.cases_succ] using congrFun (ih (fun j => b j.succ)) j

theorem write_read (n : Nat) (b : (qubits n).Basis) : writeBits n (readBits b) = b := by
  induction n with
  | zero => cases b; rfl
  | succ n ih =>
    rcases b with ⟨b,r⟩
    change (b, writeBits n (readBits r)) = (b,r)
    rw [ih]

def bitStringEquiv (n : Nat) : (qubits n).Basis ≃ (Fin n → Fin 2) where
  toFun := readBits
  invFun := writeBits n
  left_inv := write_read n
  right_inv := read_write n

instance (n : Nat) : Nonempty (qubits n).Basis := ⟨writeBits n (fun _ => 0)⟩

def bitGate : BB84Basis → Operator .bit
  | .Z => 1
  | .X => hadamard

theorem bitGate_adjoint (θ : BB84Basis) : (bitGate θ).conjTranspose = bitGate θ := by
  cases θ with
  | Z => exact Matrix.conjTranspose_one
  | X => exact hadamard_adjoint

theorem bitGate_square (θ : BB84Basis) : bitGate θ * bitGate θ = 1 := by
  cases θ with
  | Z => exact Matrix.one_mul _
  | X => exact hadamard_square

theorem tensor_isometry {a b c d : Space} (M : Op a b) (N : Op c d)
    (hM : M.conjTranspose * M = 1) (hN : N.conjTranspose * N = 1) :
    (Op.tensor M N).conjTranspose * Op.tensor M N = 1 := by
  unfold Op.tensor Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hM, hN]
  exact Matrix.one_kronecker_one

def blockGate : (n : Nat) → (Fin n → BB84Basis) → Operator (qubits n)
  | 0, _ => 1
  | n+1, θ => Op.tensor (bitGate (θ 0)) (blockGate n (fun i => θ i.succ))

theorem blockGate_adjoint (n : Nat) (θ : Fin n → BB84Basis) :
    (blockGate n θ).conjTranspose = blockGate n θ := by
  induction n with
  | zero => simp [blockGate]
  | succ n ih =>
    calc
      _ = Op.tensor (Op.dagger (bitGate (θ 0)))
          (Op.dagger (blockGate n (fun i => θ i.succ))) := Op.dagger_tensor _ _
      _ = _ := congrArg₂ Op.tensor (bitGate_adjoint (θ 0)) (ih _)

theorem blockGate_isometry (n : Nat) (θ : Fin n → BB84Basis) :
    (blockGate n θ).conjTranspose * blockGate n θ = 1 := by
  induction n with
  | zero => simp [blockGate]
  | succ n ih =>
    apply tensor_isometry
    · rw [bitGate_adjoint, bitGate_square]
    · exact ih _

theorem blockGate_square (n : Nat) (θ : Fin n → BB84Basis) :
    blockGate n θ * blockGate n θ = 1 := by
  calc
    _ = (blockGate n θ).conjTranspose * blockGate n θ := by rw [blockGate_adjoint]
    _ = 1 := blockGate_isometry n θ

def blockBasisChannel (n : Nat) (θ : Fin n → BB84Basis) : Channel (qubits n) (qubits n) :=
  Channel.ofIsometry (blockGate n θ) (blockGate_isometry n θ)

def blockPrepare (n : Nat) (θ : Fin n → BB84Basis) (b : Fin n → Fin 2) : Density (qubits n) :=
  (blockBasisChannel n θ).run (basisDensity (qubits n) (writeBits n b))

/-- Matched decoding recovers the whole basis state, not just its individual marginals. -/
theorem block_matched_matrix (n : Nat) (θ : Fin n → BB84Basis) (b : Fin n → Fin 2) :
    ((blockBasisChannel n θ).run (blockPrepare n θ b)).matrix =
      (basisDensity (qubits n) (writeBits n b)).matrix := by
  simp only [blockPrepare, blockBasisChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply,
    blockGate_adjoint]
  calc
    _ = (blockGate n θ * blockGate n θ) * (basisDensity (qubits n) (writeBits n b)).matrix *
        (blockGate n θ * blockGate n θ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [blockGate_square, Matrix.one_mul, Matrix.mul_one]

end
end Foundation.Quantum.QKD
