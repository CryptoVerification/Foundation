import Foundation.Quantum.QKD.ReconciliationCorrectness
import Foundation.Quantum.QKD.PairwiseReconciliationPrivacy
import Foundation.Quantum.QKD.RelabelRestricted
import Foundation.Quantum.QKD.GuessExamples

/-! A full-weight coherent CQ input with one real bit error in every block.
This verifies the concrete decoder; it is not a BB84 attack simulation. -/
namespace Foundation.Quantum.QKD.RepetitionReconciliationExamples
noncomputable section
open RepetitionReconciliation Subnormalized
set_option backward.isDefEq.respectTransparency false

def inputLabel (k : Fin 2) : (Fin 1 → Triple) × (Fin 1 → Triple) :=
  (fun _ => ![k,k,k], fun _ => ![k+1,k,k])

def outputLabel (k : Fin 2) : ((Fin 1 → Triple) × (Fin 1 → Triple)) × (Fin (1*2) → Fin 2) :=
  ((fun _ => ![k,k,k], fun _ => ![k,k,k]), fun _ => 0)

theorem input_error : ∀ k : Fin 2,
    errors ((inputLabel k).1 0) ((inputLabel k).2 0) = 1 := by decide

theorem decoded_label : ∀ k : Fin 2, reconcile (inputLabel k) = outputLabel k := by decide

def source := ofCQ (Guessing.hideLeak GuessExamples.coherentState)
def input := relabel source inputLabel

theorem output_eq : process input = relabel source outputLabel := by
  unfold process input
  rw [relabel_comp]
  congr 1
  funext k
  exact decoded_label k

theorem normalized : mass (process input) = 1 := by
  rw [process_mass, input, mass_relabel]
  exact mass_ofCQ _

theorem correct : CommonKey.correctnessError (process input) = 0 := by
  rw [output_eq]
  have h : restrict (relabel source outputLabel) (fun x => x.1.1 ≠ x.1.2) =
      relabel (restrict source (fun _ => False)) outputLabel := by
    rw [restrict_relabel]
    rfl
  have he : CommonKey.correctnessError (relabel source outputLabel) =
      mass (restrict (relabel source outputLabel) (fun x => x.1.1 ≠ x.1.2)) := by
    rw [mass_restrict]
    unfold CommonKey.correctnessError
    apply Finset.sum_congr rfl
    intro x _
    by_cases hc : x.1.1 = x.1.2 <;> simp [hc]
  rw [he, h, mass_relabel, mass_restrict]
  simp

/-- The quantum side register is retained with a nonzero off-diagonal entry. -/
theorem retained_coherence :
    (process input).block (outputLabel 0) 0 1 = 1/4 := by
  rw [output_eq]
  have h : (fun _ : Fin 1 => ![(1 : Fin 2),1,1]) ≠ (fun _ : Fin 1 => ![(0 : Fin 2),0,0]) := by decide
  norm_num [relabel, Matrix.sum_apply, Fin.sum_univ_two, source, ofCQ,
    Guessing.hideLeak, GuessExamples.coherentState, GuessExamples.revealedBit,
    outputLabel, Matrix.smul_apply, prepare_plus_matrix, h]

end
end Foundation.Quantum.QKD.RepetitionReconciliationExamples
