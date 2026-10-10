import Foundation.Quantum.QKD.SubnormalizedLogic
import Foundation.Quantum.QKD.SubnormalizedPublic
import Foundation.Quantum.QKD.GuessExamples
import Foundation.Quantum.Channels

/-! A concrete selective branch with mass 1/2. It retains a coherent qubit,
then an actual dephasing channel removes that coherence. Weighted optimal
success remains 1/2; impossible branches have zero success. This is a self-made
validation example, not an asserted BB84 security estimate. -/
namespace Foundation.Quantum.QKD.SubnormalizedExamples
noncomputable section
open scoped ComplexOrder
open Guessing (constantMeasurement)
open Subnormalized
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

abbrev Label := Fin 2 × Fin 2

def initial : State Label .bit := ofCQ GuessExamples.coherentState

def branch : State Label .bit := restrict initial (fun p => p = (0,0))

def processed : State Label .bit := post branch (dephase .bit)

theorem initial_dominated : Subnormalized.Dominated initial (prepare .X 0) (1/2) := by
  intro p
  simp only [initial, ofCQ, GuessExamples.coherentState, GuessExamples.revealedBit]
  rw [show ((1/2:ℝ):ℂ) = (1/2:ℂ) by push_cast; rfl]
  by_cases h : p.1 = p.2
  · simp only [h, ite_true, sub_self]
    exact Matrix.PosSemidef.zero
  · simp only [h, ite_false, sub_zero]
    exact (prepare .X 0).positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)

theorem branch_mass : mass branch = 1/2 := by
  unfold branch
  rw [mass_restrict]
  simp [initial, ofCQ, GuessExamples.coherentState, GuessExamples.revealedBit,
    Matrix.trace_smul, (prepare .X 0).normalized]

theorem branch_probability : probability branch = 1/2 := by
  apply le_antisymm
  · simpa only [branch_mass] using probability_le_mass branch
  · have h := score_le_probability branch (constantMeasurement (0,0))
    rw [score_constantMeasurement] at h
    simpa [branch, restrict, initial, ofCQ, GuessExamples.coherentState,
      GuessExamples.revealedBit, Matrix.trace_smul, (prepare .X 0).normalized] using h

theorem processed_mass : mass processed = 1/2 := by
  unfold processed
  rw [mass_post, branch_mass]

theorem processed_probability : probability processed = 1/2 := by
  apply le_antisymm
  · exact (probability_post branch (dephase .bit)).trans_eq branch_probability
  · have h := score_le_probability processed (constantMeasurement (0,0))
    rw [score_constantMeasurement] at h
    simpa [processed, post, (dephase .bit).toKraus.trace_apply, (dephase .bit).complete,
      branch, restrict, initial, ofCQ, GuessExamples.coherentState,
      GuessExamples.revealedBit, Matrix.trace_smul, (prepare .X 0).normalized] using h

theorem branch_coherence : branch.block (0,0) 0 1 = 1/4 := by
  norm_num [branch, restrict, initial, ofCQ, GuessExamples.coherentState,
    GuessExamples.revealedBit, Matrix.smul_apply, prepare_plus_matrix]

theorem processed_coherence : processed.block (0,0) 0 1 = 0 := by
  simp [processed, post, dephase, Kraus.apply, projector, Matrix.mul_apply,
    Matrix.conjTranspose_apply,
    Fin.sum_univ_two]

theorem impossible_mass : mass (restrict initial (fun _ => False)) = 0 := by
  simp [mass_restrict]

theorem impossible_probability : probability (restrict initial (fun _ => False)) = 0 :=
  probability_zero_mass _ impossible_mass

def proof : Derivation (SubnormalizedLogic.presentation Label)
    (Logic.Context.singleton (.domination (.state 0) 0 (1/2)))
      (.guessBound (.process (.select (.state 0) {(0,0)}) 0) (1/2)) :=
  SubnormalizedLogic.selectProcess 0 0 0 {(0,0)} (1/2)

theorem interpreted :
    (SubnormalizedLogic.model (fun _ => initial) (fun _ => dephase .bit) (fun _ => prepare .X 0)).Carrier
      (.guessBound (.process (.select (.state 0) {(0,0)}) 0) (1/2)) := by
  apply SubnormalizedLogic.sound (fun _ => initial) (fun _ => dephase .bit) (fun _ => prepare .X 0) proof
  intro _
  exact initial_dominated

/-- Public information is retained, and all joint measurements are allowed.
The success probability is still 1/2 per original execution, rather than one. -/
theorem branch_public_probability : probability (withPublic branch) = 1/2 := by
  apply le_antisymm
  · exact (public_probability_le_mass branch).trans_eq branch_mass
  · have h := leakScore_le_probability branch (fun l => constantMeasurement l)
    have hs : leakScore branch (fun l => constantMeasurement l) = 1/2 := by
      norm_num [leakScore, branch, restrict, initial, ofCQ, GuessExamples.coherentState,
        GuessExamples.revealedBit, constantMeasurement, ite_mul, Matrix.trace_smul,
        (prepare .X 0).normalized, Fin.sum_univ_two]
    rw [hs] at h
    exact h

end
end Foundation.Quantum.QKD.SubnormalizedExamples
