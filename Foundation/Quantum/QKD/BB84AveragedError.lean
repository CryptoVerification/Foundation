import Foundation.Quantum.QKD.BB84ErrorLogic
import Foundation.Quantum.QKD.BB84Instrument

/-! Uniform-bit error probabilities in each BB84 basis. These are true
single-signal conditional probabilities, not empirical estimates from a
finite sample. Sampling error remains a separate protocol obligation. -/
namespace Foundation.Quantum.QKD.BB84Attack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

def bitError (V : BB84Attack e) (θ : BB84Basis) (b : Fin 2) : ℝ :=
  (measurementEffect θ (1-b)).probability (V.bobChannel.run (prepare θ b))

/-- The conditional error probability when the input bit is unbiased. -/
def basisError (V : BB84Attack e) (θ : BB84Basis) : ℝ :=
  (V.bitError θ 0 + V.bitError θ 1) / 2

theorem bitError_nonneg (V : BB84Attack e) (θ : BB84Basis) (b : Fin 2) : 0 ≤ V.bitError θ b :=
  (measurementEffect θ (1-b)).probability_nonneg _

theorem bitError_le_twice_basis (V : BB84Attack e) (θ : BB84Basis) (b : Fin 2) :
    V.bitError θ b ≤ 2 * V.basisError θ := by
  unfold basisError
  fin_cases b
  · change V.bitError θ 0 ≤ 2 * ((V.bitError θ 0 + V.bitError θ 1) / 2)
    linarith [V.bitError_nonneg θ 1]
  · change V.bitError θ 1 ≤ 2 * ((V.bitError θ 0 + V.bitError θ 1) / 2)
    linarith [V.bitError_nonneg θ 0]

theorem bitError_Z (V : BB84Attack e) (b : Fin 2) : V.bitError .Z b = V.zError b := by
  have hp : (prepare .Z b).matrix = (basisDensity .bit b).matrix := by
    simp [prepare, basisChannel, Channel.identity, Channel.ofIsometry, Channel.run]
  have he : (measurementEffect .Z (1-b)).matrix = (basisEffect .bit (1-b)).matrix := by
    simp [measurementEffect, basisChannel, Channel.identity, Channel.ofIsometry,
      Channel.pullEffect, Kraus.dual, Kraus.single]
  unfold bitError Effect.probability
  rw [he]
  change ((basisEffect .bit (1-b)).matrix * V.bobChannel.toKraus.apply (prepare .Z b).matrix).trace.re = _
  rw [hp]
  exact V.zError_probability b

theorem bitError_X_zero (V : BB84Attack e) : V.bitError .X 0 = V.xPlusError := by
  simpa only [bitError, sub_zero] using V.xPlusError_probability

/-- Each actual classical error event has precisely the Born probability used above. -/
theorem bitError_outcome (V : BB84Attack e) (θ : BB84Basis) (b : Fin 2) :
    Foundation.Probability.eventProb (V.signalOutcome θ θ b) (fun r => r = 1-b) =
      ENNReal.ofReal (V.bitError θ b) := V.signalOutcome_event θ θ b (1-b)

/-- Both BB84 bases use all bit values, without replacing the plus error by the average silently. -/
theorem averaged_environment_bound (V : BB84Attack e) (E : Effect e) :
    |E.probability (V.environmentState 0) - E.probability (V.environmentState 1)| ≤
      4 * Real.sqrt (2 * V.basisError .X) +
        4 * Real.sqrt (2 * V.basisError .Z) + 4 * V.basisError .Z := by
  have h0 : V.zError 0 ≤ 2 * V.basisError .Z := by
    rw [← V.bitError_Z 0]
    exact V.bitError_le_twice_basis .Z 0
  have h1 : V.zError 1 ≤ 2 * V.basisError .Z := by
    rw [← V.bitError_Z 1]
    exact V.bitError_le_twice_basis .Z 1
  have hx : V.xPlusError ≤ 2 * V.basisError .X := by
    rw [← V.bitError_X_zero]
    exact V.bitError_le_twice_basis .X 0
  have h := (V.environment_test_bound_zero_one E).trans (bb84PrivacyError_mono h0 h1 hx)
  exact h.trans_eq (by unfold bb84PrivacyError; ring)

/-- The measured upper-bound hypotheses needed by the finite-error calculus follow from the averages. -/
theorem averaged_test_hypotheses (V : BB84Attack e) (τ : Nat → Channel e e) : ∀ i,
    (BB84ErrorLogic.model (fun _ => V) τ).Carrier
      ((BB84ErrorLogic.testContext 0 (2 * V.basisError .Z) (2 * V.basisError .Z)
        (2 * V.basisError .X)).claim i) := by
  intro i
  fin_cases i
  · change (basisEffect .bit 1).probability (V.bobChannel.run (basisDensity .bit 0)) ≤ _
    have h := V.bitError_le_twice_basis .Z 0
    rw [V.bitError_Z] at h
    simpa only [← zError_probability, sub_zero] using h
  · change (basisEffect .bit 0).probability (V.bobChannel.run (basisDensity .bit 1)) ≤ _
    have h := V.bitError_le_twice_basis .Z 1
    rw [V.bitError_Z] at h
    simpa only [← zError_probability, sub_self] using h
  · change (measurementEffect .X 1).probability (V.bobChannel.run (prepare .X 0)) ≤ _
    have h := V.bitError_le_twice_basis .X 0
    simpa only [bitError, sub_zero] using h

/-- Uniform-bit basis errors instantiate an actual derivation, including arbitrary postprocessing. -/
theorem averaged_proof_interpreted (V : BB84Attack e) (τ : Nat → Channel e e)
    (t : BB84ErrorLogic.Processing) :
    (BB84ErrorLogic.model (fun _ => V) τ).Carrier
      (.leakage 0 (.seq .identity t)
        (bb84PrivacyError (2 * V.basisError .Z) (2 * V.basisError .Z) (2 * V.basisError .X))) :=
  BB84ErrorLogic.sound (fun _ => V) τ
    (BB84ErrorLogic.processedProof 0 _ _ _ t) (V.averaged_test_hypotheses τ)

end
end Foundation.Quantum.QKD.BB84Attack
