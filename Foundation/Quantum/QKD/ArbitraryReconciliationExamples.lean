import Foundation.Quantum.QKD.ArbitraryReconciliationCQ
import Foundation.Quantum.QKD.ReconciliationExamples

/-! Seven-bit example: one error in each full triple plus an erroneous
suffix bit. The full-weight quantum side information retains coherence.
This is a decoder example, not an independent BB84 noise/security assumption. -/
namespace Foundation.Quantum.QKD.ArbitraryReconciliationExamples
noncomputable section
open ArbitraryReconciliation Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def alice (k : Fin 2) : Word 7 := ![k,k,k,k,k,k,k]
def bob (k : Fin 2) : Word 7 := ![k+1,k,k,k,k+1,k,k+1]

theorem block_errors : ∀ k : Fin 2, ∀ j : Fin (7/3),
    RepetitionReconciliation.errors (block (alice k) j) (block (bob k) j) = 1 := by decide

theorem total_errors : ∀ k : Fin 2,
    (Finset.univ.filter (fun i => alice k i ≠ bob k i)).card = 3 := by decide

theorem decoded : ∀ k : Fin 2, decode (bob k) (message (alice k)) = alice k := by
  intro k
  exact decode_correct _ _ (fun j => by rw [block_errors])

theorem disclosed_bits : publicBits 7 = 5 := by decide

theorem message_alphabet : Fintype.card (Message 7) = 32 := by
  rw [message_card, disclosed_bits]
  norm_num

def inputLabel (k : Fin 2) : (Word 7 × Word 7) × Unit := ((alice k,bob k),())
def outputLabel (k : Fin 2) := ((alice k,alice k),((),message (alice k)))
def source := ofCQ (Guessing.hideLeak GuessExamples.coherentState)
def input := relabel source inputLabel

theorem output_eq : process input = relabel source outputLabel := by
  unfold process input
  rw [relabel_comp]
  congr 1
  funext k
  simp only [Function.comp_def, inputLabel, decoded]
  rfl

theorem normalized : mass (process input) = 1 := by
  rw [process_mass, input, mass_relabel]
  exact mass_ofCQ _

theorem correct : CommonKey.correctnessError (process input) = 0 := by
  rw [VerifiedHash.correctness_mass, output_eq, restrict_relabel, mass_relabel, mass_restrict]
  simp only [outputLabel, ne_eq, not_true_eq_false, ite_false, Finset.sum_const_zero]

theorem retained_coherence : (process input).block (outputLabel 0) 0 1 = 1/4 := by
  rw [output_eq]
  have h : outputLabel 1 ≠ outputLabel 0 := by decide
  norm_num [relabel, Matrix.sum_apply, Fin.sum_univ_two, source, ofCQ,
    Guessing.hideLeak, GuessExamples.coherentState, GuessExamples.revealedBit,
    Matrix.smul_apply, prepare_plus_matrix, h]

theorem verified_correctness : CommonKey.correctnessError (verified (tag := 8) input) ≤ 1/256 := by
  have h := ArbitraryReconciliation.verified_correctness (tag := 8) input
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin] at h ⊢
  exact h

end
end Foundation.Quantum.QKD.ArbitraryReconciliationExamples
