import Foundation.Crypto.Logic.Polygraph.ApproximateGameCoherence
import Foundation.Crypto.Logic.Polygraph.QuantitativeRecovery
import Foundation.Crypto.Logic.Polygraph.NativeCompiledRecovery

/-! A positive-error recovery four-cell for the five-state edge, together
with its nonzero lower bound, sequential contexts, and the zero-error native
two-to-five-state witness embedded without changing its original proof. -/
namespace CryptoLogic.Polygraph.Experiment.ApproximateRecovery
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance sourceFintype (event : Fin 5 → Prop) : Fintype (RecoveryRigidity.sourceGame event).Outcome :=
  inferInstanceAs (Fintype (Fin 5))
local instance targetFintype (event : Fin 5 → Prop) : Fintype (RecoveryRigidity.targetGame event).Outcome :=
  inferInstanceAs (Fintype (Fin 5))
local instance nativeSourceFintype (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    Fintype (NativeRecoverable.sourceGame message event).Outcome := inferInstanceAs (Fintype Bool)

def stationaryStep (event : Fin 5 → Prop) :
    Step (RecoveryRigidity.sourceGame event) (RecoveryRigidity.sourceGame event) :=
  { Step.ofMap _ _ id (PMF.map_id _) (fun _ _ => Iff.rfl) with
    loss := 3 / 128
    bound := by
      change eventProb _ (fun _ => False) ≤ _
      simp [eventProb] }

def stationary (event : Fin 5 → Prop) :
    GameCoherence.Path (RecoveryRigidity.sourceGame event) (RecoveryRigidity.sourceGame event) := .step (stationaryStep event)

theorem discrepancy_is_error (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : GameCoherence.Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : GameCoherence.Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent)) :
    FiniteKernelVariation.distance (RecoveryRigidity.sourceGame sourceEvent).program.eval
      (GameCoherence.Path.seq forward reverse).kernel (stationary sourceEvent).kernel =
      QuantitativeRecovery.pathError sourceEvent targetEvent forward reverse := by
  change FiniteKernelVariation.distance
    (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
      Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source)
    (fun x => (forward.kernel x).bind reverse.kernel) (fun x => PMF.pure x) = _
  simp only [FiniteKernelVariation.distance,FiniteKernelVariation.variation_pure,
    QuantitativeRecovery.pathError,FiniteRecoveryError.failure,FiniteRecoveryError.different_probability]
  rfl

theorem example_discrepancy (event : Fin 5 → Prop) :
    FiniteKernelVariation.distance (RecoveryRigidity.sourceGame event).program.eval
      (QuantitativeRecovery.exampleRoundtrip event).kernel (stationary event).kernel = 5719 / 253440 := by
  rw [QuantitativeRecovery.exampleRoundtrip,discrepancy_is_error,QuantitativeRecovery.example_error]

def recoveryCell (event : Fin 5 → Prop) :
    ApproximateGameCoherence.Cell4 (QuantitativeRecovery.exampleRoundtrip event) (stationary event)
      (5719 / 253440) := by
  apply ApproximateGameCoherence.Cell4.generator
  constructor
  · rw [example_discrepancy]
  · change (QuantitativeRecovery.exampleRoundtrip event).loss = 3 / 128
    exact QuantitativeRecovery.example_loss event

theorem example_minimal_tolerance (event : Fin 5 → Prop) (δ : ℝ)
    (cell : ApproximateGameCoherence.Cell4 (QuantitativeRecovery.exampleRoundtrip event) (stationary event) δ) :
    5719 / 253440 ≤ δ := by
  have h := cell.sound.kernel_bound
  rw [example_discrepancy] at h
  exact h

theorem required_tolerance (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : GameCoherence.Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : GameCoherence.Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent))
    (δ : ℝ) (cell : ApproximateGameCoherence.Cell4 (.seq forward reverse) (stationary sourceEvent) δ) :
    3 / 256 ≤ δ := by
  have h := cell.sound.kernel_bound
  rw [discrepancy_is_error] at h
  exact QuantitativeRecovery.required_tolerance sourceEvent targetEvent forward reverse δ h

theorem no_zero_cell (sourceEvent targetEvent : Fin 5 → Prop)
    (forward : GameCoherence.Path (RecoveryRigidity.sourceGame sourceEvent) (RecoveryRigidity.targetGame targetEvent))
    (reverse : GameCoherence.Path (RecoveryRigidity.targetGame targetEvent) (RecoveryRigidity.sourceGame sourceEvent)) :
    IsEmpty (ApproximateGameCoherence.Cell4 (.seq forward reverse) (stationary sourceEvent) 0) := by
  constructor
  intro cell
  have h := required_tolerance sourceEvent targetEvent forward reverse 0 cell
  norm_num at h

def contextual {before after : Observed} [Fintype before.Outcome] [Fintype after.Outcome]
    (event : Fin 5 → Prop) (beforePath : GameCoherence.Path before (RecoveryRigidity.sourceGame event))
    (afterPath : GameCoherence.Path (RecoveryRigidity.sourceGame event) after) :
    ApproximateGameCoherence.Cell4
      (.seq (.seq beforePath (QuantitativeRecovery.exampleRoundtrip event)) afterPath)
      (.seq (.seq beforePath (stationary event)) afterPath) (5719 / 253440) :=
  ApproximateGameCoherence.Cell4.contextual beforePath (recoveryCell event) afterPath

def exactNativeAsApprox (message : Bool) (event : Machine.NativePreparedState.State → Prop) :
    ApproximateGameCoherence.Cell4 (NativeCompiledRecovery.roundtrip message event)
      (NativeRecoverable.stationary message event) 0 :=
  .exact (NativeCompiledRecovery.recoveryCell message event)

end
end CryptoLogic.Polygraph.Experiment.ApproximateRecovery
