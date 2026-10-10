import Foundation.Quantum.QKD.BB84PhaseSampling
import Foundation.Quantum.QKD.SourceReplacementExamples

/-! An actual computational-basis eavesdropper in complementary coordinates.
The test is nontrivial and preserves Eve's coherence within an accepted
sample value. These examples are independent validation constructions. -/
namespace Foundation.Quantum.QKD.PhaseSamplingExamples
noncomputable section
open BB84PhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev attack := SourceReplacementExamples.attack

def coordinate (b e a : Fin 2) : (BB84PurifiedSource.jointSpace attack).Basis :=
  ((((b,()),e),Fintype.equivFin Unit ()),(a,()))

theorem amplitude (b e a : Fin 2) :
    vector attack (coordinate b e a) =
      if e = 1 ∧ b ≠ a then -hadamardCoefficient^3 else hadamardCoefficient^3 := by
  simp only [vector, BB84PurifiedSource.vector, Channel.pureDilationVector, Matrix.mulVec, dotProduct, pow_one]
  change (∑ p : ((((Fin 2 × Unit) × Fin 2) × Fin 1) × (Fin 2 × Unit)),
    gate 1 .bit (.register 1) (coordinate b e a) p *
      (∑ q : (Fin 2 × Unit) × (Fin 2 × Unit),
        (Op.tensor attack.dilation (Op.ident (qubits 1))) p q *
          SourceReplacement.pairVector (qubits 1) hadamardCoefficient q)) = _
  have hd : attack.dilation = fun i j => SourceReplacementExamples.dilation i.1 j := rfl
  rw [hd]
  have h01 : ((0,()) : (qubits 1).Basis) ≠ (1,()) := by decide
  have h10 := Ne.symm h01
  have he : (Fintype.equivFin Unit) () = (0 : Fin 1) := by
    apply Fin.ext
    change ((Fintype.equivFin Unit) ()).val = 0
    have hc : Fintype.card Unit = 1 := Fintype.card_unique
    have hh := ((Fintype.equivFin Unit) ()).isLt
    omega
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  fin_cases b <;> fin_cases e <;> fin_cases a <;>
    norm_num [h01, h10, he, Space.Basis, qubits, Prod.mk.injEq, gate, coordinate, SourceReplacementExamples.dilation,
      SourceReplacement.pairVector, Op.tensor, Op.ident, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.one_apply, blockGate, bitGate, hadamard] <;> ring

theorem phase_coherence :
    (state attack).matrix (coordinate 0 0 0) (coordinate 0 1 0) = 1/8 := by
  rw [pure]
  change vector attack (coordinate 0 0 0) * star (vector attack (coordinate 0 1 0)) = _
  rw [amplitude, amplitude]
  norm_num [star_pow, ← mul_pow, hadamardCoefficient_square]

def tested : Finset (Fin 1) := {0}

def zeros : TestRecord 1 := (fun _ => some 0, fun _ => some 0)

theorem accepted_zeros : accepts zeros := by intro i; rfl

/-- The actual nonempty sample records both zero bits, while Eve's
off-diagonal entry remains 1/8 rather than being silently dephased. -/
theorem measured_coherence :
    ((measurement .bit (.register (Fintype.card attack.index)) tested).branch
      (Fintype.equivFin (TestRecord 1) zeros)).apply (state attack).matrix
        (coordinate 0 0 0) (coordinate 0 1 0) = 1/8 := by
  rw [measurement_entry]
  have h (e : Fin 2) : label tested (coordinate 0 e 0) = zeros := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  rw [h, h, if_pos ⟨rfl,rfl⟩, phase_coherence]

theorem interpreted :
    (QuantumSamplingLogic.model (Sampling.sample (Finset.univ : Finset (Fin 1)) 1 (by decide))
      (QuantumErrorSampling.good Finset.univ 1 pattern) (vector attack) (unit attack)
      (fun _ => BB84PhaseSampling.fallback attack) (BB84PhaseSampling.channels attack)).Carrier
      (.processed 0 (Real.sqrt (Sampling.missedErrorBound (Finset.univ : Finset (Fin 1)) 1 1).toReal)) :=
  BB84PhaseSampling.interpreted attack Finset.univ 1 1 (by decide)

/-- An actual arbitrary-length basis eavesdropper. This is the isometry
|x⟩ ↦ |x,x⟩ on basis states, and entangles their superpositions. -/
def copyAttack (n : Nat) : BlockAttack n (qubits n) :=
  Channel.ofIsometry (Op.copy (qubits n)) (by
    simpa only [Op.seq, Op.dagger, Op.ident] using Op.copy_special (qubits n))

theorem finite_bound :
    (Sampling.missedErrorBound (Finset.univ : Finset (Fin 2)) 1 1).toReal = 1/2 := by
  norm_num [Sampling.missedErrorBound]

/-- Two attacked signals, one sampled signal and a genuine nonzero quantum
error bound. This is a sampling conclusion, not a claim of final-key secrecy. -/
theorem interpreted_two :
    (QuantumSamplingLogic.model (Sampling.sample (Finset.univ : Finset (Fin 2)) 1 (by decide))
      (QuantumErrorSampling.good Finset.univ 1 pattern) (vector (copyAttack 2)) (unit (copyAttack 2))
      (fun _ => BB84PhaseSampling.fallback (copyAttack 2)) (BB84PhaseSampling.channels (copyAttack 2))).Carrier
      (.processed 0 (Real.sqrt (1/2))) := by
  have h := BB84PhaseSampling.interpreted (copyAttack 2) Finset.univ 1 1 (by decide)
  rw [finite_bound] at h
  exact h

end
end Foundation.Quantum.QKD.PhaseSamplingExamples
