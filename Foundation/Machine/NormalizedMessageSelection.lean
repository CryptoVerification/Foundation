import Foundation.Machine.SelectedMessagePreparation
import Foundation.Machine.NormalizationInvocation

namespace Machine.GuardedCompiler

/-- The actual guarded normalizer result already has the native selector's
end-of-response layout. This equality does not reload, decode or replace
any tape: both the copied response and the source scratch are retained. -/
theorem rawResultFrom_selectedMessageStart (normalizer : Program) (input : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Configuration)
    (first second state : List Bool)
    (hOutput : c.outputBits = canonicalMessageBits first second state) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: savedInput) c).swapTapes
    returned.resumeAt 0 = prepareMessageSelectionStart savedInput returned.outputTape.left
      first second state (2 * c.outputTape.cells + 2 - c.outputBits.length) := by
  change c.outputTape.bits = canonicalMessageBits first second state at hOutput
  simp [rawResultFrom, extractOutputFinish, copyScratchFinish, Configuration.swapTapes,
    Configuration.resumeAt, prepareMessageSelectionStart, Configuration.outputBits,
    hOutput]

/-- Invoke the fixed native selector/copy program directly from a returned
normalizer branch. The successful source output must be canonical, as
established by the normalization certificate. The selected message and the
native random bit coexist with all saved physical caller cells. -/
theorem selectNormalizedMessage_eval (normalizer : Program) (input : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Configuration)
    (first second state : List Bool)
    (hOutput : c.outputBits = canonicalMessageBits first second state) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: savedInput) c).swapTapes
    evalConfigWithin prepareSelectedMessage (returned.resumeAt 0)
      (prepareSelectedMessageSteps first second state) =
      Foundation.Probability.sampleBit.map
        (prepareSelectedMessageFinish savedInput returned.outputTape.left first second state
          (2 * c.outputTape.cells + 2 - c.outputBits.length)) := by
  dsimp only
  rw [rawResultFrom_selectedMessageStart normalizer input beforeInput savedInput c first second state hOutput]
  exact prepareSelectedMessage_eval _ _ _ _ _ _

/-- Runtime safety does not require a canonical normalizer response. The
actual guarded result, including its saved caller cells and source scratch,
is passed directly to the native selector/copy stage. In particular this
also covers normalizer results for malformed public input, where the
normalizer's valid-instance correctness certificate cannot be used. -/
theorem selectNormalizedMessage_haltsFrom (normalizer : Program) (input : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Configuration) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: savedInput) c).swapTapes
    ∀ finish, PaddedRunsFor prepareSelectedMessage (returned.resumeAt 0) finish
      (400 * (returned.inputTape.cells + returned.outputTape.cells) + 500) →
      finish.halted = true := by
  dsimp only
  intro finish run
  exact prepareSelectedMessage_haltsFrom_anyTape _ _ finish run

/-- The guarded result's physical scratch tape is a fresh output frontier
for the selector. Every resulting random branch retains a fresh frontier
for native request assembly, without a canonical-message output premise. -/
theorem selectNormalizedMessage_output_layout (normalizer : Program) (input : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Configuration) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: savedInput) c).swapTapes
    ∀ finish, PaddedRunsFor prepareSelectedMessage (returned.resumeAt 0) finish
      (400 * (returned.inputTape.cells + returned.outputTape.cells) + 500) →
      ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  dsimp only
  intro finish run
  exact prepareSelectedMessage_output_layout_anyTape _ _ 0 finish run


/-- Arbitrary returned normalizer bits, including an empty or malformed
response, remain a finite raw frontier after selection and field copying.
The native selector never obtains extra valid-format assumptions here. -/
theorem selectNormalizedMessage_input_raw_frontier (normalizer : Program) (input : List Bool)
    (beforeInput savedInput : List (Option Bool)) (c : Configuration) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: savedInput) c).swapTapes
    ∀ finish, PaddedRunsFor prepareSelectedMessage (returned.resumeAt 0) finish
      (400 * (returned.inputTape.cells + returned.outputTape.cells) + 500) →
      ∃ (remaining : List Bool) (padding : Nat),
        finish.inputTape.current :: finish.inputTape.right =
          remaining.map some ++ none :: List.replicate padding none := by
  dsimp only
  intro finish run
  exact prepareSelectedMessage_input_raw_frontier _ _ []
    (2 * c.outputTape.cells + 2 - c.outputBits.length) rfl finish run

end Machine.GuardedCompiler
