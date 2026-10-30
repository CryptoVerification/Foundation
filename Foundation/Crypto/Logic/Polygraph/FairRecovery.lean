import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecovery
import Foundation.Crypto.Logic.Polygraph.ApproximateRecovery
import Foundation.Crypto.Logic.Polygraph.ApproximateDiagramEdits

/-! The finitely fair replacement kernels are genuine directed game paths.
Both endpoint distributions stay exact, with explicitly changed local losses.
The positive-error recovery cell is not a native runtime certificate. -/
namespace CryptoLogic.Polygraph.Experiment.FairRecoveryGame
open Foundation.Probability GameCoherence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance sourceFintype (event : Fin 5 → Prop) : Fintype (RecoveryRigidity.sourceGame event).Outcome :=
  inferInstanceAs (Fintype (Fin 5))

def countedStep (p q : PMF (Fin 5)) (event : Fin 5 → Prop) (kernel : Fin 5 → PMF (Fin 5))
    (preserve : p.bind kernel = q) (budget : ℝ)
    (exactBudget : FiniteRecoveryError.failure p kernel PMF.pure = budget) :
    Step (FiniteMaximal.game p event) (FiniteMaximal.game q event) where
  kernel := kernel
  preserve := preserve
  bad pair := pair.1 ≠ pair.2
  agree x _ y _ good := by
    have same : x = y := not_ne_iff.mp good
    subst y
    rfl
  loss := ENNReal.ofReal budget
  bound := by
    have h := (FiniteRecoveryError.failure_identity_joint p kernel).symm.trans exactBudget
    have finite : eventProb (p.bind fun x => (kernel x).map fun y => (x,y)) (fun pair => pair.1 ≠ pair.2) ≠ ∞ :=
      ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp))
    have eq := congrArg ENNReal.ofReal h
    rw [ENNReal.ofReal_toReal finite] at eq
    exact eq.le

def forward (event : Fin 5 → Prop) :
    GameCoherence.Path (RecoveryRigidity.sourceGame event) (RecoveryRigidity.targetGame event) :=
  .step (countedStep _ _ event FairRecovery.forward FairRecovery.forward_preserve
    (6961 / 524288) FairRecovery.forward_mismatch)

def reverse (event : Fin 5 → Prop) :
    GameCoherence.Path (RecoveryRigidity.targetGame event) (RecoveryRigidity.sourceGame event) :=
  .step (countedStep _ _ event FairRecovery.reverse FairRecovery.reverse_preserve
    (12499 / 1048576) FairRecovery.reverse_mismatch)

def roundtrip (event : Fin 5 → Prop) := GameCoherence.Path.seq (forward event) (reverse event)

def stationaryStep (event : Fin 5 → Prop) :
    Step (RecoveryRigidity.sourceGame event) (RecoveryRigidity.sourceGame event) :=
  { Step.ofMap _ _ id (PMF.map_id _) (fun _ _ => Iff.rfl) with
    loss := ENNReal.ofReal (26421 / 1048576)
    bound := by
      change eventProb _ (fun _ => False) ≤ _
      simp [eventProb] }

def stationary (event : Fin 5 → Prop) := GameCoherence.Path.step (stationaryStep event)

theorem roundtrip_loss (event : Fin 5 → Prop) : (roundtrip event).loss = ENNReal.ofReal (26421 / 1048576) := by
  change ENNReal.ofReal (6961 / 524288) + ENNReal.ofReal (12499 / 1048576) = _
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

theorem discrepancy (event : Fin 5 → Prop) :
    FiniteKernelVariation.distance (RecoveryRigidity.sourceGame event).program.eval
      (roundtrip event).kernel (stationary event).kernel = 13037041 / 536870912 := by
  change FiniteKernelVariation.distance (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw
    Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source)
    (fun x => (FairRecovery.forward x).bind FairRecovery.reverse) (fun x => PMF.pure x) = _
  simp only [FiniteKernelVariation.distance, FiniteKernelVariation.variation_pure]
  have h := FairRecovery.recovery_error
  unfold FiniteRecoveryError.failure at h
  simp only [FiniteRecoveryError.different_probability] at h
  exact h

def recoveryCell (event : Fin 5 → Prop) :
    ApproximateGameCoherence.Cell4 (roundtrip event) (stationary event) (13037041 / 536870912 : ℝ) :=
  .generator ⟨by rw [discrepancy], roundtrip_loss event⟩

def recoveryEdit (event : Fin 5 → Prop) :
    ApproximateDiagramEdits.Edit (DiagramBridge.diagram (roundtrip event))
      (DiagramBridge.diagram (stationary event)) (13037041 / 536870912 : ℝ) := by
  apply ApproximateDiagramEdits.Edit.game
  simp only [DiagramBridge.evaluate_diagram]
  exact recoveryCell event

theorem error_exceeds_selected_example : (5719 / 253440 : ℝ) < 13037041 / 536870912 := by norm_num

theorem loss_exceeds_selected_example : (3 / 128 : ℝ) < 26421 / 1048576 := by norm_num

end
end CryptoLogic.Polygraph.Experiment.FairRecoveryGame
