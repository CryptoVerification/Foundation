import Foundation.Examples.MixedCircuitFusionRepair

/-! The previously certified nonconfluent pair is joined in the extended
catalogue. Also exercise macro elimination in copy/discard contexts and
reuse of the old mixed critical cell. No global confluence is asserted. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def repairedFusionPath (stage : Nat) : Path (relators := rules) (fusionAssociated stage) (fusionDirect stage) :=
  .cons (suffixStep (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage))
    (.cons (embedStep (.seqLeft (wireChange (.root (.leftUnit _))) _)) (.refl _))

def repairedFusionJoin (stage : Nat) :
    Σ destination, Path (relators := rules) (fusionDirect stage) destination × Path (relators := rules) (fusionAssociated stage) destination :=
  ⟨fusionDirect stage, .refl _, repairedFusionPath stage⟩

theorem repairedFusionPath_support (stage : Nat) : Path.support (repairedFusionPath stage) = {stage + 1} := by
  simp [repairedFusionPath, Path.support, embedStep_support, suffixStep_support,
    Step.support, wireChange, Primitive.support, Relator.support, Structural.rules,
    fusionDirect, after, Circuit.needs, signature, MACNormalization.layout]

def copiedCritical (stage : Nat) :=
  (criticalCell (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage)).whisker
    (Placement.seqLeft (.wire (.copy finish)))

def discardedCritical (stage : Nat) :=
  (criticalCell (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage)).whisker
    (Placement.seqLeft (.wire (.discard finish)))

theorem copiedCritical_support (stage : Nat) : PresentedCell.support (copiedCritical stage) = {stage + 1} := by
  simp [copiedCritical, PresentedCell.whisker_support, criticalCell_support,
    Placement.needs, after, Circuit.needs, signature, MACNormalization.layout]

theorem discardedCritical_support (stage : Nat) : PresentedCell.support (discardedCritical stage) = {stage + 1} := by
  simp [discardedCritical, PresentedCell.whisker_support, criticalCell_support,
    Placement.needs, after, Circuit.needs, signature, MACNormalization.layout]

def oldMACComparison (stage : Nat) := embedCell (reuseCompletion (Structural.criticalCell stage (.wire copy)))

theorem oldMACComparison_support (stage : Nat) : PresentedCell.support (oldMACComparison stage) = {stage, stage + 1} := by
  rw [oldMACComparison, embedCell_support, reuseCompletion_support, Structural.criticalCell_support]
  simp [Circuit.needs]

def copiedElimination (stage : Nat) :=
  eliminateTrack ((Placement.seqLeft (.wire (.copy finish))).track
    (.step (suffixStep (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage))))

theorem copiedElimination_support (stage : Nat) : PresentedCell.support (copiedElimination stage).cell = {stage + 1} := by
  rw [copiedElimination, eliminateTrack_support, Placement.track_support]
  simp [RewriteTrack.support, suffixStep_support, Placement.needs, after, Circuit.needs, signature, MACNormalization.layout]

def roundTripElimination (stage : Nat) :=
  let path := Track.step (suffixStep (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage))
  eliminateTrack (.comp path (.inv path))

theorem roundTripElimination_support (stage : Nat) : PresentedCell.support (roundTripElimination stage).cell = {stage + 1} := by
  rw [roundTripElimination, eliminateTrack_support]
  simp [RewriteTrack.support, suffixStep_support, after, Circuit.needs, signature, MACNormalization.layout]

def reusedExpandedComparison (stage : Nat) :=
  let path := Track.step (suffixStep (.identity (source (stage + 1))) (.identity (source (stage + 1))) (after stage))
  let oldComparison : MixedCell (expandTrack path) (expandTrack (embedTrack (expandTrack path))) := by
    rw [expand_embedTrack]
    exact .refl _
  liftCoherence path (embedTrack (expandTrack path)) oldComparison

theorem reusedExpandedComparison_support (stage : Nat) : PresentedCell.support (reusedExpandedComparison stage) = {stage + 1} := by
  rw [reusedExpandedComparison, liftCoherence_support]
  simp [PresentedCell.support, expandTrack_support, RewriteTrack.support, suffixStep_support,
    after, Circuit.needs, signature, MACNormalization.layout]

/-- info: (0, 2, 1, 1, 12, 12) -/
#guard_msgs in
#eval ((repairedFusionJoin 0).2.1.length, (repairedFusionJoin 0).2.2.length,
  (PresentedCell.support (copiedCritical 0)).card, (PresentedCell.support (discardedCritical 0)).card,
  PresentedCell.constructorCount (copiedCritical 0), PresentedCell.constructorCount (discardedCritical 0))

/-- info: (2, 12, 1) -/
#guard_msgs in
#eval ((PresentedCell.support (oldMACComparison 0)).card,
  PresentedCell.constructorCount (oldMACComparison 0),
  (PresentedCell.support (copiedElimination 0).cell).card)

/-- info: (1, 1, 1) -/
#guard_msgs in
#eval ((PresentedCell.support (roundTripElimination 0).cell).card,
  (PresentedCell.support (reusedExpandedComparison 0)).card,
  (PresentedCell.support (projectCell (reusedExpandedComparison 0)).cell).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
