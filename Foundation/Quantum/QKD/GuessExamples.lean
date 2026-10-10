import Foundation.Quantum.QKD.CQRepresentation
import Foundation.Quantum.QKD.GuessProcessing
import Foundation.Quantum.QKD.GuessPublic
import Foundation.Quantum.QKD.GuessEntropy
import Foundation.Quantum.QKD.GuessLogic

/-! Tight one-bit public leakage with a retained coherent quantum system.
Prior optimal guessing is 1/2; revealing the bit makes it exactly one.
The matrix domination premise of the finite derivation is discharged here. -/
namespace Foundation.Quantum.QKD.GuessExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic
open Guessing
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

/-- A uniform bit copied to a public classical register, with arbitrary
 normalized quantum side information independent of that bit. -/
def revealedBit (σ : Density e) : CQ (Fin 2 × Fin 2) e where
  block p := if p.1 = p.2 then (1/2 : ℂ) • σ.matrix else 0
  positive p := by
    split_ifs
    · exact σ.positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)
    · exact Matrix.PosSemidef.zero
  normalized := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace_smul, σ.normalized]

theorem prior_block (σ : Density e) (x : Fin 2) :
    (hideLeak (revealedBit σ)).block x = (1/2 : ℂ) • σ.matrix := by
  simp [hideLeak, revealedBit]

theorem prior_dominated (σ : Density e) : Dominated (hideLeak (revealedBit σ)) σ (1/2) := by
  intro x
  rw [prior_block]
  norm_num
  exact Matrix.PosSemidef.zero

theorem prior_guessing (σ : Density e) : guessingProbability (hideLeak (revealedBit σ)) = 1/2 := by
  apply le_antisymm
  · exact guessingProbability_le_of_dominated _ σ (1/2) (prior_dominated σ)
  · have h := score_le_guessingProbability (hideLeak (revealedBit σ)) (constantMeasurement 0)
    rw [score_constantMeasurement, prior_block, Matrix.trace_smul, σ.normalized] at h
    norm_num at h ⊢
    exact h

theorem reveal_score (σ : Density e) : leakScore (revealedBit σ) (fun l => constantMeasurement l) = 1 := by
  norm_num [leakScore, constantMeasurement, revealedBit, ite_mul, Matrix.trace_smul, σ.normalized, Fin.sum_univ_two]

theorem revealed_guessing (σ : Density e) : leakedGuessingProbability (revealedBit σ) = 1 := by
  apply le_antisymm
  · have h := leakage_of_dominated (revealedBit σ) σ (1/2) (prior_dominated σ)
    norm_num at h ⊢
    exact h
  · have h := leakScore_le_optimal (revealedBit σ) (fun l => constantMeasurement l)
    rw [reveal_score] at h
    exact h

/-- An actual composite derivation is interpreted with a proved matrix premise. -/
theorem leak_derivation_interpreted (σ : Density e) :
    (GuessLogic.model (fun _ => revealedBit σ) (fun _ => σ)).Carrier
      (.leakedOptimal 0 (2*(1/2))) := by
  apply GuessLogic.sound (fun _ => revealedBit σ) (fun _ => σ) (GuessLogic.leakProof 2 0 0 (1/2))
  intro i
  exact prior_dominated σ

/-- A concrete coherent qubit, retained without replacing it by a classical distribution. -/
def coherentState : CQ (Fin 2 × Fin 2) .bit := revealedBit (prepare .X 0)

theorem coherent_prior_guessing : guessingProbability (hideLeak coherentState) = 1/2 := prior_guessing _
theorem coherent_revealed_guessing : leakedGuessingProbability coherentState = 1 := revealed_guessing _

/-- Off-diagonal quantum coherence survives the joint classical representation. -/
theorem coherent_joint_entry :
    coherentState.density.matrix (Fintype.equivFin (Fin 2 × Fin 2) (0,0),0)
      (Fintype.equivFin (Fin 2 × Fin 2) (0,0),1) = 1/4 := by
  rw [CQ.density_block]
  norm_num [coherentState, revealedBit, Matrix.smul_apply, prepare_plus_matrix]

/-- A completely general joint measurement, including the public bit and
retained coherent qubit, has optimal success exactly one. -/
theorem coherent_public_joint_guessing :
    guessingProbability (withPublic coherentState) = 1 := by
  rw [withPublic_optimal, coherent_revealed_guessing]

/-- The operational entropy of the hidden uniform bit is exactly one bit. -/
theorem coherent_hidden_entropy : guessingEntropy (hideLeak coherentState) = 1 := by
  unfold guessingEntropy
  rw [coherent_prior_guessing]
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  norm_num

/-- The public bit removes that operational entropy, even though the
independent coherent quantum system remains in the actual joint state. -/
theorem coherent_public_entropy : publicGuessingEntropy coherentState = 0 := by
  unfold publicGuessingEntropy guessingEntropy
  rw [coherent_public_joint_guessing]
  simp

end
end Foundation.Quantum.QKD.GuessExamples
