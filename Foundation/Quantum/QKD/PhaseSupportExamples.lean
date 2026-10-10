import Foundation.Quantum.QKD.BB84PhaseSupport
import Foundation.Quantum.QKD.LinearHash

/-! A three-signal coherent example with a retained, entangled qubit. The
complementary support contains two strings. Neither the domination premise nor
the quantum secrecy conclusion is assumed. This is a constructed example,
not a sampled BB84 execution. -/
namespace Foundation.Quantum.QKD.PhaseSupportExamples
noncomputable section
set_option backward.isDefEq.respectTransparency false

def zero : (qubits 3).Basis := (0,(0,(0,())))
def other : (qubits 3).Basis := (1,(0,(0,())))
def support : Finset (qubits 3).Basis := {zero,other}
theorem distinct : zero ≠ other := by decide

def vectors (i : (qubits 3).Basis) (u : Fin 2) : ℂ :=
  if u = i.1 then hadamardCoefficient else 0

theorem normalized : (∑ i ∈ support, CoherentSupport.outer (e := .bit) (vectors i)).trace = 1 := by
  simp only [support, Finset.sum_pair distinct, Matrix.trace_add]
  change (∑ u : Fin 2, vectors zero u * star (vectors zero u)) +
    (∑ u : Fin 2, vectors other u * star (vectors other u)) = 1
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [vectors, zero, other, starRingEnd_apply, hadamardCoefficient_square]

def output : Guessing.CQ (qubits 3).Basis .bit := PhaseSupport.state (e := .bit) 3 support vectors normalized

theorem reference_matrix : (CoherentSupport.reference (e := .bit) support vectors normalized).matrix =
    (1/2:ℂ) • (1 : Operator .bit) := by
  ext i j
  simp only [CoherentSupport.reference, support, Finset.sum_pair distinct, Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [CoherentSupport.reference, support, zero, other, vectors, CoherentSupport.outer,
      Matrix.vecMulVec_apply, Matrix.sum_apply, Pi.star_apply, Matrix.smul_apply,
      Matrix.one_apply, starRingEnd_apply, hadamardCoefficient_star, hadamardCoefficient_square]

theorem coefficient : PhaseSupport.bound 3 support = 1/4 := by
  simp only [PhaseSupport.bound, support, Finset.card_pair distinct]
  norm_num

theorem dominated : Subnormalized.Dominated (Subnormalized.ofCQ output)
    (CoherentSupport.reference (e := .bit) support vectors normalized) (1/4) := by
  rw [← coefficient]
  exact PhaseSupport.dominated (e := .bit) 3 support vectors normalized

theorem guessing : Subnormalized.probability (Subnormalized.ofCQ output) ≤ 1/4 := by
  rw [← coefficient]
  exact PhaseSupport.guessing (e := .bit) 3 support vectors normalized

/-- Eve retains an actual nonzero off-diagonal conditional matrix entry. -/
theorem coherence : output.block zero 0 1 = 1/16 := by
  have h4 : hadamardCoefficient^4 = (1/4:ℂ) := by
    calc
      _ = (hadamardCoefficient*hadamardCoefficient)*(hadamardCoefficient*hadamardCoefficient) := by ring
      _ = _ := by rw [hadamardCoefficient_square]; norm_num
  have h8 : hadamardCoefficient^8 = (1/16:ℂ) := by
    calc
      _ = hadamardCoefficient^4 * hadamardCoefficient^4 := by ring
      _ = _ := by rw [h4]; norm_num
  simp only [output, PhaseSupport.state, CoherentSupport.measured, CoherentSupport.outer,
    Matrix.vecMulVec_apply, Pi.star_apply, CoherentSupport.amplitude, support, Finset.sum_pair distinct,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [ PhaseSupport.state, CoherentSupport.measured, CoherentSupport.outer,
    Matrix.vecMulVec_apply, Pi.star_apply, CoherentSupport.amplitude, Finset.sum_apply,
    support, zero, other, vectors, PhaseSupport.gate, blockGate, bitGate, hadamard,
    Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply]
  convert h8 using 1
  ring

/-- The input has coherent correlations across the signal and auxiliary systems. -/
theorem input_cross_entry : (PhaseSupport.input (e := .bit) 3 support vectors normalized).matrix
    (zero,0) (other,1) = 1/2 := by
  norm_num [PhaseSupport.input, CoherentSupport.outer, Matrix.vecMulVec_apply, Pi.star_apply,
    PhaseSupport.inputVector, support, zero, other, vectors, starRingEnd_apply, hadamardCoefficient_star, hadamardCoefficient_square]


def encode (x : (qubits 3).Basis) : Hashing.Bits (Fin 3) :=
  fun i => ZMod.finEquiv 2 (readBits x i)

theorem encode_injective : Function.Injective encode := by
  intro x y h
  apply (bitStringEquiv 3).injective
  funext i
  exact (ZMod.finEquiv 2).injective (congrFun h i)

abbrev Seeds := Hashing.Seed (Fin 3) (Fin 1)
abbrev Key := Hashing.Bits (Fin 1)
def hash (s : Seeds) (x : (qubits 3).Basis) : Key := Hashing.linearHash s (encode x)

theorem collision (x y : (qubits 3).Basis) (hxy : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform Seeds) hash x y ≤ 1 / Fintype.card Key := by
  have hh := Hashing.linear_collision (O := Fin 1) (encode x) (encode y)
    (fun heq => hxy (encode_injective heq))
  simpa only [Collision.collision, hash, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat] using le_of_eq hh

/-- The finite meta-logical derivation is interpreted on these actual matrices,
with a concrete random binary linear hash and its public seed. -/
theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform Seeds)
        (fun s => Collision.hashed (Subnormalized.ofCQ output).block (hash s)))
      (publicMixture (Foundation.Probability.uniform Seeds)
        (fun _ => Collision.uniformComparator (Y := Key) (Subnormalized.ofCQ output).block)) (1/4) := by
  have hh := PhaseSupport.privacy (e := .bit) 3 support vectors normalized
    (Foundation.Probability.uniform Seeds) hash collision
  change OperatorApprox _ _ _ at hh
  convert hh using 1
  · rfl
  · rfl
  · have hr : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [Key, Hashing.Bits, coefficient, Fintype.card_fun, Fintype.card_fin, ZMod.card, Real.sqrt_div, hr]

end
end Foundation.Quantum.QKD.PhaseSupportExamples
