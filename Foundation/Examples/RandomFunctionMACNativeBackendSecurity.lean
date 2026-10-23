import Foundation.Examples.RandomFunctionMACNativeBackend
import Foundation.Constructions.Hash.NativeCompactMACGame

/-! Security of the full native ideal backend execution for the SAME MAC.
The keyed comparison uses the existing concrete caller and explicit extracted
distinguisher. Its keyed oracle evaluation remains an external capability;
this file does not implement or time a native keyed function evaluator. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.NativeBackend
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Hash.Native CompactMACRound CompactMACExecution
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

variable {State Source : Type}
    (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (serverState : State) (callerState : Source)

noncomputable def idealGame : PMF Bool :=
  (TimedExecution.eval (CompactMACRound.step oracle callerOracle) 2091
    (.source (NativeCode.frame serverState [] emptyMachine) ⟨callerState, .running {}, []⟩)).map physicalVerdict

theorem idealGame_eq_lazy :
    idealGame oracle callerOracle serverState callerState = (target.run RandomOracle.oracle []).map Outcome.result :=
  runtime_verdict_law oracle callerOracle (empty serverState []) callerState [] rfl 2091 (by simp [empty])

theorem idealGame_eq_family :
    idealGame oracle callerOracle serverState callerState = Native.familyGame (uniform (Message → Tag)) id := by
  rw [idealGame_eq_lazy]
  symm
  simp only [Native.familyGame, Native.verdict_law, id_eq]
  rw [← PMF.map_bind, RandomOracle.eager_lazy]

/-- The reference of the explicit cached distinguisher is the full physical
ideal execution, including adaptive requests and the actual final comparison. -/
theorem idealGame_eq_distinguisher :
    idealGame oracle callerOracle serverState callerState =
      RandomFunctionMACSchedules.idealExperiment
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack) := by
  rw [idealGame_eq_family, Native.family_game_eq]
  simpa only [RandomFunctionMACSchedules.idealExperiment, RandomFunctionMACSchedules.familyExperiment, id_eq] using
    (RandomFunctionMACProofEdits.cached_family_eq (uniform (Message → Tag)) id
      RandomFunctionMACSchedules.Examples.attack).symm

theorem ideal_security :
    eventProb (idealGame oracle callerOracle serverState callerState) (· = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [idealGame_eq_family]
  exact Native.ideal_security

/-- The existing keyed caller is compared against the newly verified
physical ideal execution under the SAME explicit PRF distinguisher premise. -/
theorem keyed_against_physical {Key : Type} (keys : PMF Key) (evaluate : Key → Message → Tag)
    (epsilon : ℝ≥0∞)
    (prf : eventProb (RandomFunctionMACSchedules.familyExperiment keys evaluate
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack)) (· = true) ≤
      eventProb (RandomFunctionMACSchedules.idealExperiment
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack)) (· = true) + epsilon) :
    eventProb (Native.familyGame keys evaluate) (· = true) ≤
      eventProb (idealGame oracle callerOracle serverState callerState) (· = true) + epsilon := by
  rw [idealGame_eq_distinguisher, Native.family_game_eq]
  rwa [RandomFunctionMACProofEdits.cached_family_eq] at prf

include oracle callerOracle serverState callerState in
theorem keyed_security {Key : Type} (keys : PMF Key) (evaluate : Key → Message → Tag)
    (epsilon : ℝ≥0∞)
    (prf : eventProb (RandomFunctionMACSchedules.familyExperiment keys evaluate
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack)) (· = true) ≤
      eventProb (RandomFunctionMACSchedules.idealExperiment
        (RandomFunctionMACProofEdits.cachedDistinguisher RandomFunctionMACSchedules.Examples.attack)) (· = true) + epsilon) :
    eventProb (Native.familyGame keys evaluate) (· = true) ≤ epsilon + (256 : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ eventProb (idealGame oracle callerOracle serverState callerState) (· = true) + epsilon :=
      keyed_against_physical oracle callerOracle serverState callerState keys evaluate epsilon prf
    _ ≤ (256 : ℝ≥0∞)⁻¹ + epsilon := add_le_add (ideal_security oracle callerOracle serverState callerState) le_rfl
    _ = _ := add_comm _ _

/-- Complete game observation, not just the verification probability:
actual private table bits and all typed request/response pairs are retained. -/
theorem ideal_game_observation :
    (TimedExecution.eval (CompactMACRound.step oracle callerOracle) 2091
      (.source (NativeCode.frame serverState [] emptyMachine) ⟨callerState, .running {}, []⟩)).map gameView =
      (target.run RandomOracle.oracle []).map (renderGame ∘ Program.mapState encodeTable) :=
  runtime_game_law oracle callerOracle (empty serverState []) callerState [] rfl 2091 (by simp [empty])

end Foundation.Symmetric.RandomFunctionMACNativeCaller.NativeBackend
