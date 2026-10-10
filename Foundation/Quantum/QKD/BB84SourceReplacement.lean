import Foundation.Quantum.DelayedSource
import Foundation.Quantum.SecondRegister
import Foundation.Quantum.QKD.BB84Block
import Foundation.Quantum.QKD.BB84KeyState

/-! Source replacement for every BB84 block length and basis string. The
source is normalized entanglement, the attack acts before Alice chooses her
basis, and the recorded outcome equals the actual uniformly weighted BB84
preparation with the attacker's whole quantum system retained. -/
namespace Foundation.Quantum.QKD.BB84Source
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem qubits_card (n : Nat) : Fintype.card (qubits n).Basis = 2^n := by
  induction n with
  | zero => simp [qubits, Space.Basis]
  | succ n ih => simp only [qubits, Space.Basis, Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

theorem coefficient (n : Nat) : hadamardCoefficient^n * star (hadamardCoefficient^n) = (1/2:ℂ)^n := by
  rw [star_pow, hadamardCoefficient_star, ← mul_pow, hadamardCoefficient_square]

theorem normalized (n : Nat) :
    (Fintype.card (qubits n).Basis:ℂ) * (hadamardCoefficient^n * star (hadamardCoefficient^n)) = 1 := by
  rw [qubits_card, coefficient, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
  norm_num

theorem bitGate_symmetric (θ : BB84Basis) (i j : Fin 2) : bitGate θ i j = bitGate θ j i := by
  cases θ with
  | Z => simp [bitGate, Matrix.one_apply, eq_comm]
  | X => simp only [bitGate, hadamard, and_comm]

theorem blockGate_symmetric (n : Nat) (θ : Fin n → BB84Basis) (i j : (qubits n).Basis) :
    blockGate n θ i j = blockGate n θ j i := by
  induction n with
  | zero => cases i; cases j; rfl
  | succ n ih =>
    rcases i with ⟨i,u⟩
    rcases j with ⟨j,w⟩
    change bitGate (θ 0) i j * blockGate n (fun k => θ k.succ) u w =
      bitGate (θ 0) j i * blockGate n (fun k => θ k.succ) w u
    rw [bitGate_symmetric, ih]

def entangled (n : Nat) : Density (.tensor (qubits n) (qubits n)) :=
  SourceReplacement.pair (qubits n) (hadamardCoefficient^n) (normalized n)

/-- The transmitted block is attacked before the source-side basis operation. -/
def state {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    Density (.tensor (.tensor (qubits n) e) (qubits n)) :=
  SourceReplacement.delayed (qubits n) (hadamardCoefficient^n) (normalized n)
    (blockGate n θ) (blockGate_isometry n θ) A

/-- Equality of the actual weighted remote density operators for every outcome. -/
theorem block {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (x : (qubits n).Basis) :
    SourceReplacement.slice (state A θ).matrix x =
      (1/2:ℂ)^n • (A.jointState θ (readBits x)).matrix := by
  have hh := SourceReplacement.delayed_replacement (qubits n) (hadamardCoefficient^n) (normalized n)
    (blockGate n θ) (blockGate_isometry n θ) (blockGate_symmetric n θ) A x
  rw [coefficient] at hh
  simpa only [state, BlockAttack.jointState, blockPrepare, blockBasisChannel, write_read] using hh

def record {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    Density (.tensor (.register (Fintype.card (qubits n).Basis)) (.tensor (qubits n) e)) :=
  (SecondRegister.channel (qubits n) (.tensor (qubits n) e)).run (state A θ)

/-- The entire physical classical-quantum record, not just the marginal of Eve. -/
theorem record_block {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (x y : (qubits n).Basis) (i j : (Space.tensor (qubits n) e).Basis) :
    (record A θ).matrix (Fintype.equivFin (qubits n).Basis x,i) (Fintype.equivFin (qubits n).Basis y,j) =
      if x = y then (1/2:ℂ)^n * (A.jointState θ (readBits x)).matrix i j else 0 := by
  change (SecondRegister.channel _ _).toKraus.apply _ _ _ = _
  rw [SecondRegister.apply_entry]
  by_cases h : x = y
  · subst y
    simpa only [if_pos rfl, ite_true, SourceReplacement.slice, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using
      congrFun (congrFun (block A θ x) i) j
  · simp only [if_neg h]


theorem weight_cast (n : Nat) : (((1/2:ℝ)^n:ℝ):ℂ) = (1/2:ℂ)^n := by
  push_cast
  rfl

open scoped ComplexOrder in
def preparedCQ {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    Guessing.CQ (qubits n).Basis (.tensor (qubits n) e) where
  block x := (1/2:ℂ)^n • (A.jointState θ (readBits x)).matrix
  positive x := (A.jointState θ (readBits x)).positive.smul (by
    have hreal : 0 ≤ (1/2:ℝ)^n := by positivity
    have hh : (0:ℂ) ≤ (((1/2:ℝ)^n:ℝ):ℂ) := Complex.nonneg_iff.mpr ⟨hreal,rfl⟩
    exact (weight_cast n) ▸ hh)
  normalized := by
    simp only [Matrix.trace_smul, (A.jointState θ _).normalized, smul_eq_mul, mul_one,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← coefficient]
    exact normalized n

/-- The physical delayed entanglement experiment and the complete classical
uniform preparation ensemble have the same joint density operator. -/
theorem record_eq {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    (record A θ).matrix = (preparedCQ A θ).density.matrix := by
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin (qubits n).Basis).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin (qubits n).Basis).surjective s
  rw [record_block, Guessing.CQ.density_block]
  rfl

theorem outcome_weight {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (x : (qubits n).Basis) :
    (SourceReplacement.slice (state A θ).matrix x).trace.re = (1/2:ℝ)^n := by
  rw [block, Matrix.trace_smul, (A.jointState θ _).normalized, ← weight_cast]
  simp only [smul_eq_mul, mul_one, Complex.ofReal_re]


theorem uniform_weight (n : Nat) (x : (qubits n).Basis) :
    (((Foundation.Probability.uniform (qubits n).Basis x).toReal:ℝ):ℂ) = (1/2:ℂ)^n := by
  simp only [Foundation.Probability.uniform, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    qubits_card, Nat.cast_pow, Nat.cast_ofNat, Complex.ofReal_inv]
  rw [one_div, inv_pow]
  norm_num only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The ordinary uniform prepare-and-send mixture, retaining Alice's bit
string as a classical register alongside Bob and Eve. -/
def ensemble {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    Density (.tensor (.register (Fintype.card (qubits n).Basis)) (.tensor (qubits n) e)) :=
  Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
    tensorDensity (basisDensity (.register (Fintype.card (qubits n).Basis))
      (Fintype.equivFin (qubits n).Basis x)) (A.jointState θ (readBits x)))

theorem ensemble_eq {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    (ensemble A θ).matrix = (preparedCQ A θ).density.matrix := by
  simp only [ensemble, Density.mixture, tensorDensity, Guessing.CQ.density, preparedCQ,
    uniform_weight]
  apply Finset.sum_congr rfl
  intro x _
  ext i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  ring

/-- Equality to the actual uniform distribution, rather than a weighting
assumed to be uniform. Every subsequent channel preserves this equality. -/
theorem uniform_replacement {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis) :
    (record A θ).matrix = (ensemble A θ).matrix :=
  (record_eq A θ).trans (ensemble_eq A θ).symm

end
end Foundation.Quantum.QKD.BB84Source
