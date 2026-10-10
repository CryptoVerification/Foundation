import Foundation.Quantum.QKD.HashDistanceLogic
import Foundation.Quantum.QKD.CollisionExamples

/-! A public hash seed and genuinely noncommuting side information. All matrix
reconstruction and numerical premises of the composed derivation are proved.
The actual and ideal joint operators differ; the observation bound is 1/2. -/
namespace Foundation.Quantum.QKD.HashDistanceExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic Collision CollisionExamples
set_option backward.isDefEq.respectTransparency false

abbrev outputSpace := Guessing.publicSpace (Fin 2) (Guessing.publicSpace (Fin 2) .bit)

def realOperator : Operator outputSpace := publicMixture seeds (fun s => hashed blocks (hash s))
def idealOperator : Operator outputSpace := publicMixture seeds (fun _ => uniformComparator (Y := Fin 2) blocks)

def proof : Derivation (HashDistanceLogic.presentation 2)
    (HashDistanceLogic.assumptions 2 0 0 (1/2) 4) (.distance 0 ((1/2:ℝ)*Real.sqrt 1)) := by
  convert HashDistanceLogic.proof 2 0 0 (1/2) 4 using 1; norm_num

theorem interpreted : OperatorApprox realOperator idealOperator (1/2) := by
  have h := HashDistanceLogic.sound seeds hash (fun _ => blocks) (fun _ => blocks_positive)
    (fun _ => 1) (fun _ => 1)
    (fun x x' hx => by simpa only [Fintype.card_fin, Nat.cast_ofNat] using le_of_eq (hash_collision x x' hx)) proof
  apply (show ((1/2:ℝ)*Real.sqrt 1) = 1/2 by norm_num) ▸ h
  intro i
  change Fin 3 at i
  by_cases h0 : i = 0
  · subst i
    change ∀ x, blocks x = (1:Operator .bit).conjTranspose * sandwich 1 blocks x * 1
    intro x
    simp [sandwich]
  · by_cases h1 : i = 1
    · subst i
      change input (sandwich (1:Operator .bit) blocks) ≤ 1/2
      have he : sandwich (1:Operator .bit) blocks = blocks := by
        funext x
        simp [sandwich]
      rw [he]
      exact le_of_eq input_value
    · have h2 : i = 2 := by omega
      subst i
      change HashDistanceLogic.cost (Y := Fin 2) (1:Operator .bit) ≤ 4
      norm_num [HashDistanceLogic.cost, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- A concrete entry witnesses that the actual published output is not ideal. -/
theorem real_entry : realOperator
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0))
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0)) = 0 := by
  unfold realOperator
  rw [publicMixture_block]
  simp only [ite_true, hashed]
  rw [ClassicalBlocks.encoded]
  norm_num [grouped, CollisionExamples.hash, Fin.sum_univ_two]

theorem ideal_entry : idealOperator
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0))
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0)) = 3/16 := by
  unfold idealOperator
  rw [publicMixture_block]
  simp only [ite_true, uniformComparator]
  rw [ClassicalBlocks.encoded]
  norm_num [seed_weight, Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_two, blocks_zero, blocks_one]

theorem actual_ne_ideal : realOperator ≠ idealOperator := by
  intro h
  have hh := congrFun (congrFun h
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0)))
    (Fintype.equivFin (Fin 2) 0,(Fintype.equivFin (Fin 2) 1,0))
  rw [real_entry, ideal_entry] at hh
  norm_num at hh

end
end Foundation.Quantum.QKD.HashDistanceExamples
