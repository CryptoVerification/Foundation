import Foundation.Crypto.Logic.Polygraph.RecoveryRigidity
import Foundation.Crypto.Logic.Polygraph.FiniteMaximalStep
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryError
import Foundation.Crypto.Semantics.Probability.ApproximateRecoveryTransport

/-! Any roundtrip through the specified five-state endpoint has averaged
source-recovery error at least 3/256. This lower bound applies to arbitrary
game paths and full-cell state kernels. Sharpness of the unconstrained finite
problem is not asserted for paths whose reverse also preserves its marginal. -/
namespace CryptoLogic.Polygraph.Experiment.QuantitativeRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section

def pathError (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent)) : ℝ :=
  FiniteRecoveryError.failure
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source) forward.kernel reverse.kernel

theorem path_error_lower (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent)) :
    3 / 256 ≤ pathError sourceEvent targetEvent forward reverse :=
  RecoveryError.recovery_error_lower forward.kernel reverse.kernel forward.preserve

theorem required_tolerance (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent))
    (δ : ℝ) (bound : pathError sourceEvent targetEvent forward reverse ≤ δ) : 3 / 256 ≤ δ :=
  (path_error_lower sourceEvent targetEvent forward reverse).trans bound

def stateError (sourcePc : ℕ) (message : Bool)
    (forward reverse : Machine.NativePreparedState.State → PMF Machine.NativePreparedState.State) : ℝ :=
  ∑ key, (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source key).toReal *
      (eventProb ((forward (RecoveryRigidity.stateView sourcePc
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message key)).bind reverse)
        (· ≠ RecoveryRigidity.stateView sourcePc
          Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message key)).toReal

theorem state_error_lower (sourcePc targetPc : ℕ) (message : Bool)
    (forward reverse : Machine.NativePreparedState.State → PMF Machine.NativePreparedState.State)
    (preserve : ((Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source).map
        (RecoveryRigidity.stateView sourcePc
          Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message)).bind forward =
      (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
        Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target).map
          (RecoveryRigidity.stateView targetPc
            Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target message)) :
    3 / 256 ≤ stateError sourcePc message forward reverse := by
  let p := Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source
  let q := Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target
  let source := RecoveryRigidity.stateView sourcePc
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source message
  let target := RecoveryRigidity.stateView targetPc
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target message
  have finite_preserve := RecoveryViewTransport.induced_preserves p q source target RecoveryRigidity.readState
    (RecoveryRigidity.state_view_inverse targetPc _ message) forward preserve
  have lower := RecoveryError.recovery_error_lower
    (RecoveryViewTransport.forward source RecoveryRigidity.readState forward)
    (RecoveryViewTransport.reverse target RecoveryRigidity.readState reverse) finite_preserve
  have transfer := ApproximateRecoveryTransport.induced_failure_le p q source target
    RecoveryRigidity.readState RecoveryRigidity.readState
    (RecoveryRigidity.state_view_inverse sourcePc _ message) (RecoveryRigidity.state_view_inverse targetPc _ message)
    forward reverse Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source_full preserve
  exact lower.trans transfer

def exampleForward (event : Fin 5 → Prop) :
    Path (RecoveryRigidity.sourceGame event) (RecoveryRigidity.targetGame event) :=
  .step (FiniteMaximal.step
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source)
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target) event)

def exampleReverse (event : Fin 5 → Prop) :
    Path (RecoveryRigidity.targetGame event) (RecoveryRigidity.sourceGame event) :=
  .step (FiniteMaximal.step
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target)
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source) event)

def exampleRoundtrip (event : Fin 5 → Prop) :
    Path (RecoveryRigidity.sourceGame event) (RecoveryRigidity.sourceGame event) :=
  .seq (exampleForward event) (exampleReverse event)

theorem example_error (event : Fin 5 → Prop) :
    pathError event event (exampleForward event) (exampleReverse event) = 5719 / 253440 :=
  RecoveryError.preserving_error

theorem example_loss (event : Fin 5 → Prop) : (exampleRoundtrip event).loss = 3 / 128 := by
  let p := Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source
  let q := Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target
  have symmetry : finiteVariation q p = finiteVariation p q := by
    unfold finiteVariation
    exact congrArg (fun r : ℝ => r / 2)
      (Finset.sum_congr rfl (fun key _ => abs_sub_comm (q key).toReal (p key).toReal))
  change ENNReal.ofReal (finiteVariation p q) + ENNReal.ofReal (finiteVariation q p) = 3 / 128
  rw [symmetry, show finiteVariation p q = 3 / 256 from RecoveryError.variation,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end
end CryptoLogic.Polygraph.Experiment.QuantitativeRecovery
