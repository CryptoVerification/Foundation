import Foundation.Crypto.Logic.Polygraph.GameProofNormalization
import Foundation.Examples.GameCoherence

/-! A common terminal suffix cannot generally be cancelled: erasing a
private bit hides two different conditional state correspondences. The
obstruction already occurs at zero statistical loss. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.NormalizationBoundary
open Foundation.Probability
open GameCoherence.Examples
set_option backward.isDefEq.respectTransparency false
noncomputable section

def terminal : Observed := privateGame (PMF.pure ())

def discard : Step fairState terminal :=
  Step.ofMap _ _ (fun _ => ()) (PMF.map_const _ _) (fun _ _ => Iff.rfl)

def completed : Cell4 (.seq (.identity fairState) (.step discard))
    (.seq (.step flipBit) (.step discard)) := by
  apply Cell4.generator
  constructor
  · intro state
    simp only [Path.kernel, discard, flipBit, Step.ofMap, PMF.pure_bind]
  · simp only [Path.loss, discard, flipBit, Step.ofMap, add_zero]

theorem suffix_cancellation_fails :
    Nonempty (Cell4 (.seq (.identity fairState) (.step discard)) (.seq (.step flipBit) (.step discard))) ∧
      ¬Nonempty (Cell4 (.identity fairState) (.step flipBit)) :=
  ⟨⟨completed⟩, no_identity_flip_comparison⟩

end
end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.NormalizationBoundary
