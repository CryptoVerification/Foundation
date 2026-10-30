import Foundation.Crypto.Logic.Polygraph.CorrelatedGameFrames

/-! Keep a bit correlated with the five-state recovery experiment. The bit
records membership in the invariant block {3,4}; it is not sampled afresh.
Forward and reverse kernels preserve that bit by their checked matrix entries. -/
namespace CryptoLogic.Polygraph.Experiment.CorrelatedRecovery
open Foundation.Probability GameCoherence CorrelatedGameFrames
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option backward.isDefEq.respectTransparency false
noncomputable section

def tag (key : Fin 5) : Bool := decide (3 ≤ key.val)

theorem forward_tag (x y : Fin 5) (hy : y ∈ (RecoveryError.attainingForward x).support) : tag y = tag x := by
  have nz : (RecoveryError.attainingForward x y).toReal ≠ 0 := by
    intro h
    exact (PMF.mem_support_iff _ _).mp hy
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right ((RecoveryError.attainingForward x).apply_ne_top y))
  rw [RecoveryError.forward_matrix] at nz
  fin_cases x <;> fin_cases y <;> norm_num [tag] at *

theorem reverse_tag (x y : Fin 5) (hy : y ∈ (RecoveryError.preservingReverse x).support) : tag y = tag x := by
  have nz : (RecoveryError.preservingReverse x y).toReal ≠ 0 := by
    intro h
    exact (PMF.mem_support_iff _ _).mp hy
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right ((RecoveryError.preservingReverse x).apply_ne_top y))
  rw [RecoveryError.reverse_matrix] at nz
  fin_cases x <;> fin_cases y <;> norm_num [tag] at *

def source (event : Fin 5 → Prop) : Frame (RecoveryRigidity.sourceGame event) Bool :=
  tagged _ tag

def target (event : Fin 5 → Prop) : Frame (RecoveryRigidity.targetGame event) Bool :=
  tagged _ tag

local instance sourceFintype (event : Fin 5 → Prop) : Fintype (RecoveryRigidity.sourceGame event).Outcome :=
  inferInstanceAs (Fintype (Fin 5))
local instance sourceFrameFintype (event : Fin 5 → Prop) (test : Bool → Prop) :
    Fintype ((source event).observed test).Outcome := inferInstanceAs (Fintype (Fin 5 × Bool))

theorem forwardCompatible (event : Fin 5 → Prop) :
    Compatible (source event) (target event) (QuantitativeRecovery.exampleForward event) :=
  by
    unfold source target
    apply compatible_tagged
    intro x _ y hy
    exact forward_tag x y hy

theorem reverseCompatible (event : Fin 5 → Prop) :
    Compatible (target event) (source event) (QuantitativeRecovery.exampleReverse event) :=
  by
    unfold source target
    apply compatible_tagged
    intro x _ y hy
    exact reverse_tag x y hy

theorem loopCompatible (event : Fin 5 → Prop) :
    Compatible (source event) (source event) (QuantitativeRecovery.exampleRoundtrip event) :=
  compatible_seq _ _ _ _ _ (forwardCompatible event) (reverseCompatible event)

theorem stationaryCompatible (event : Fin 5 → Prop) :
    Compatible (source event) (source event) (ApproximateRecovery.stationary event) := by
  apply compatible_tagged
  intro x _ y hy
  have same : y = x := (PMF.mem_support_pure_iff _ _).mp hy
  subst y
  rfl

def roundtrip (event : Fin 5 → Prop) (test : Bool → Prop) :=
  lift (source event) (source event) test (QuantitativeRecovery.exampleRoundtrip event) (loopCompatible event)

def stationary (event : Fin 5 → Prop) (test : Bool → Prop) :=
  lift (source event) (source event) test (ApproximateRecovery.stationary event) (stationaryCompatible event)

def recoveryCell (event : Fin 5 → Prop) (test : Bool → Prop) :
    ApproximateGameCoherence.Cell4 (roundtrip event test) (stationary event test) (5719 / 253440 : ℝ) :=
  liftCell _ _ test (ApproximateRecovery.recoveryCell event) (loopCompatible event) (stationaryCompatible event)

theorem discrepancy (event : Fin 5 → Prop) (test : Bool → Prop) :
    FiniteKernelVariation.distance ((source event).observed test).program.eval
      (roundtrip event test).kernel (stationary event test).kernel = 5719 / 253440 := by
  rw [roundtrip, stationary, lift_distance, ApproximateRecovery.example_discrepancy]

end
end CryptoLogic.Polygraph.Experiment.CorrelatedRecovery
