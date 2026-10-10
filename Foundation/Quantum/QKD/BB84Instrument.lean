import Foundation.Quantum.QKD.BB84Basis
import Foundation.Quantum.InstrumentMarginal
import Foundation.Quantum.QKD.BB84Complementary
import Foundation.Quantum.ProbabilityBridge

/-! BB84 measurements as instruments with physical classical records. The
quantum output, including a retained environment, is not replaced by a PMF. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem projector_adjoint (a : Space) (r : a.Basis) :
    (projector a r).conjTranspose = projector a r := by
  ext i j
  by_cases hi : i = r <;> by_cases hj : j = r <;>
    simp_all [projector, Matrix.conjTranspose_apply]

theorem projector_square (a : Space) (r : a.Basis) :
    projector a r * projector a r = projector a r := by
  ext i j
  by_cases hi : i = r <;> by_cases hj : j = r <;>
    simp_all [projector, Matrix.mul_apply, ite_and, mul_ite, eq_comm]

def computationalInstrument : Instrument .bit .bit 2 where
  branch r := Kraus.single (projector .bit r)
  complete := by simpa only [Kraus.single_effect] using projector_complete .bit

theorem computational_probability (ρ : Density .bit) (r : Fin 2) :
    computationalInstrument.probability ρ r = (basisEffect .bit r).probability ρ := by
  unfold Instrument.probability
  rw [Instrument.branch_trace]
  simp only [computationalInstrument, Kraus.single_effect]
  change ((projector .bit r).conjTranspose * projector .bit r * ρ.matrix).trace.re = _
  rw [projector_adjoint, projector_square]
  rfl

/-- The basis is chosen before the projective measurement; outcomes are physical branches. -/
def measurementInstrument (θ : BB84Basis) : Instrument .bit .bit 2 :=
  computationalInstrument.pre (basisChannel θ)

theorem measurement_probability (θ : BB84Basis) (ρ : Density .bit) (r : Fin 2) :
    (measurementInstrument θ).probability ρ r = (measurementEffect θ r).probability ρ := by
  rw [measurementInstrument, Instrument.pre_probability, computational_probability,
    Effect.probability_run]
  rfl

/-- Recording the outcome retains both the measured qubit and every environment index. -/
def measurementRecord (θ : BB84Basis) (e : Space) :
    Channel (.tensor .bit e) (.tensor (.register 2) (.tensor .bit e)) :=
  ((measurementInstrument θ).amplify e).record

theorem measurementRecord_normalized (θ : BB84Basis) (e : Space)
    (ρ : Density (.tensor .bit e)) : ((measurementRecord θ e).run ρ).matrix.trace = 1 :=
  ((measurementRecord θ e).run ρ).normalized

/-- Only the classical marginal is exposed to the existing probability interface. -/
def measurementOutcome (θ : BB84Basis) (ρ : Density .bit) : Foundation.Probability.ProbComp (Fin 2) :=
  (measurementInstrument θ).classicalOutcome ρ

theorem measurementOutcome_event (θ : BB84Basis) (ρ : Density .bit) (r : Fin 2) :
    Foundation.Probability.eventProb (measurementOutcome θ ρ) (fun s => s = r) =
      ENNReal.ofReal ((measurementEffect θ r).probability ρ) := by
  rw [measurementOutcome, Instrument.classicalOutcome_event, measurement_probability]

namespace BB84Attack
variable {e : Space}

/-- A concrete signal has a physical outcome register and a retained quantum environment. -/
def signalRecord (V : BB84Attack e) (alice bob : BB84Basis) (b : Fin 2) :
    Density (.tensor (.register 2) (.tensor .bit e)) :=
  (V.jointChannel.seq (measurementRecord bob e)).run (prepare alice b)

/-- The classical marginal of this measurement is compatible with the existing PMF interface. -/
def signalOutcome (V : BB84Attack e) (alice bob : BB84Basis) (b : Fin 2) :
    Foundation.Probability.ProbComp (Fin 2) :=
  ((measurementInstrument bob).amplify e).classicalOutcome
    (V.jointChannel.run (prepare alice b))

theorem signalOutcome_event (V : BB84Attack e) (alice bob : BB84Basis) (b r : Fin 2) :
    Foundation.Probability.eventProb (V.signalOutcome alice bob b) (fun s => s = r) =
      ENNReal.ofReal ((measurementEffect bob r).probability (V.bobChannel.run (prepare alice b))) := by
  rw [signalOutcome, Instrument.classicalOutcome_event, Instrument.amplify_probability,
    measurement_probability]
  congr 1
  unfold Effect.probability
  rw [bobChannel, Channel.seq_run_matrix]

theorem zError_outcome (V : BB84Attack e) (b : Fin 2) :
    Foundation.Probability.eventProb (V.signalOutcome .Z .Z b) (fun s => s = 1-b) =
      ENNReal.ofReal (V.zError b) := by
  rw [signalOutcome_event]
  have hp : (prepare .Z b).matrix = (basisDensity .bit b).matrix := by
    simp [prepare, basisChannel, Channel.identity, Channel.ofIsometry, Channel.run]
  have he : (measurementEffect .Z (1-b)).matrix = (basisEffect .bit (1-b)).matrix := by
    simp [measurementEffect, basisChannel, Channel.identity, Channel.ofIsometry,
      Channel.pullEffect, Kraus.dual, Kraus.single]
  congr 1
  unfold Effect.probability
  rw [he]
  change ((basisEffect .bit (1-b)).matrix * V.bobChannel.toKraus.apply (prepare .Z b).matrix).trace.re = _
  rw [hp]
  exact V.zError_probability b

theorem xPlusError_outcome (V : BB84Attack e) :
    Foundation.Probability.eventProb (V.signalOutcome .X .X 0) (fun s => s = 1) =
      ENNReal.ofReal V.xPlusError := by
  rw [signalOutcome_event, V.xPlusError_probability]

end BB84Attack

end
end Foundation.Quantum.QKD
