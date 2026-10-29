import Foundation.Crypto.Semantics.Probability.FiniteObserverVariation
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitCertifiedComparison

/-! The checked finite edge distance bounds every probabilistic observation of
the key/ciphertext pair. Keys are included, so this is not a key-hidden claim. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Foundation.Probability
open scoped BigOperators ENNReal

theorem tableEightBitLaw_mass (v : OrderedGridVertex 32) (message : Bool) (result : Fin 5 × Bool) :
    tableEightBitLaw v message result =
      eventProb (tableEightBitLaw v message) (· = result) := by
  symm
  exact PMF.toOuterMeasure_apply_singleton _ _

theorem table_finiteVariation_eq (u v : OrderedGridVertex 32) (message : Bool) :
    finiteVariation (tableEightBitLaw u message) (tableEightBitLaw v message) =
      tableEightBitJointDistance u v message := by
  unfold finiteVariation tableEightBitJointDistance
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, tableEightBitLaw_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro key _
  ring

theorem table_probabilistic_event_edge_bound {α : Type} (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool)
    (next : (Fin 5 × Bool) → PMF α) (event : α → Prop) :
    probabilityGap (eventProb ((tableEightBitLaw u message).bind next) event)
      (eventProb ((tableEightBitLaw v message).bind next) event) ≤ (37 / 128 : ℝ≥0∞) := by
  have h := probabilistic_event_bound (tableEightBitLaw u message) (tableEightBitLaw v message) next event
  rw [table_finiteVariation_eq] at h
  have hu := ENNReal.ofReal_le_ofReal (table_experiment_edge_upper u v he message)
  have hcast : ENNReal.ofReal (37 / 128 : ℝ) = (37 / 128 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hcast] at hu
  exact h.trans hu

theorem table_all_observers_edge_bound (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    ObserverBound (fun _ => True) (tableEightBitLaw u message) (tableEightBitLaw v message)
      (37 / 128 : ℝ≥0∞) := by
  intro observer _
  exact table_probabilistic_event_edge_bound u v he message observer (· = true)

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
