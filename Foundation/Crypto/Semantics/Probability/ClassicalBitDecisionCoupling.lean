import Foundation.Crypto.Semantics.Probability.FiniteBooleanThreshold
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitKeyTest

/-! Explicit common-draw couplings for the decision observable at every grid
vertex. This retains the chosen Boolean view, not the full private state. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Foundation.Probability
open scoped BigOperators ENNReal

def decisionCount (v : OrderedGridVertex 32) (message : Bool) : ℕ :=
  ∑ result, if keyPairTest result = true then tableAtomCount v message result else 0

theorem decisionCount_le (v : OrderedGridVertex 32) (message : Bool) : decisionCount v message ≤ 256 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (eventProb_le_one ((tableEightBitLaw v message).map keyPairTest) (· = true))
  rw [event_real_count] at h
  change (decisionCount v message : ℝ) / 256 ≤ (1 : ℝ) at h
  have hr : (decisionCount v message : ℝ) ≤ 256 := by linarith
  exact_mod_cast hr

theorem decision_threshold_marginal (v : OrderedGridVertex 32) (message : Bool) :
    (tableEightBitLaw v message).map keyPairTest =
      FiniteBooleanThreshold.law (decisionCount v message) := by
  apply FiniteBooleanThreshold.bool_ext_true_real
  rw [event_real_count, FiniteBooleanThreshold.true_probability _ (decisionCount_le v message)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  rfl

def decisionBad (u v : OrderedGridVertex 32) (message : Bool) : Fin 256 → Prop :=
  FiniteBooleanThreshold.bad (decisionCount u message) (decisionCount v message)

theorem decisionBad_probability (u v : OrderedGridVertex 32) (message : Bool) :
    eventProb (uniform (Fin 256)) (decisionBad u v message) =
      probabilityGap (eventProb ((tableEightBitLaw u message).map keyPairTest) (· = true))
        (eventProb ((tableEightBitLaw v message).map keyPairTest) (· = true)) := by
  unfold decisionBad
  rw [FiniteBooleanThreshold.bad_eq_gap _ _ (decisionCount_le u message) (decisionCount_le v message),
    ← decision_threshold_marginal, ← decision_threshold_marginal]

theorem decisionBad_edge_bound (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    eventProb (uniform (Fin 256)) (decisionBad u v message) ≤ (37 / 128 : ℝ≥0∞) := by
  rw [decisionBad_probability]
  have h := table_all_observers_edge_bound u v he message (fun result => PMF.pure (keyPairTest result)) trivial
  simpa only [observerGap, PMF.map, Function.comp_def] using h

theorem decisionBad_sharp (message : Bool) :
    eventProb (uniform (Fin 256)) (decisionBad (sharpTableChain 0) (sharpTableChain 2) message) =
      (37 / 128 : ℝ≥0∞) := by
  rw [decisionBad_probability, keyPair_gap]

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
