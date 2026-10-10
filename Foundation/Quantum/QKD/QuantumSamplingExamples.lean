import Foundation.Quantum.QKD.QuantumSamplingLogic
import Foundation.Quantum.QKD.QuantumErrorTest
import Foundation.Quantum.QKD.BB84Basis

/-! A coherent entangled two-qubit example for the sampling calculus. The
public fair bit selects one of two good subspaces. Both good and omitted mass
are one half. This is a constructed sampling instance, not a complete BB84
parameter-estimation experiment. -/
namespace Foundation.Quantum.QKD.QuantumSamplingExamples
noncomputable section
open PureProjection Foundation.Logic
set_option backward.isDefEq.respectTransparency false

abbrev joint := Space.tensor .bit .bit

def bell (i : joint.Basis) : ℂ := if i.1 = i.2 then hadamardCoefficient else 0

theorem normalized : bracket (e := joint) bell bell = 1 := by
  simp only [bracket, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [bell, starRingEnd_apply, hadamardCoefficient_square]

def good (s : Fin 2) (i : joint.Basis) : Prop := i.1 = s
instance (s : Fin 2) : DecidablePred (good s) := fun _ => inferInstanceAs (Decidable (_ = _))
def fallback (s : Fin 2) : joint.Basis := (s,s)
def distribution : PMF (Fin 2) := Foundation.Probability.uniform (Fin 2)

theorem classical (i : joint.Basis) :
    (Foundation.Probability.eventProb distribution (fun s => ¬ good s i)).toReal ≤ 1/2 := by
  rw [eventProb_toReal]
  rcases i with ⟨i,j⟩
  fin_cases i <;> norm_num [good, distribution, Fin.sum_univ_two,
    Foundation.Probability.uniform, PMF.uniformOfFintype_apply]

theorem omitted (s : Fin 2) : mass (SupportProjection.drop (good s) bell) = 1/2 := by
  rw [QuantumSampling.omitted_mass]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases s <;>
    norm_num [good, QuantumSampling.weight, bell,
      starRingEnd_apply, hadamardCoefficient_square]

theorem retained (s : Fin 2) : mass (SupportProjection.keep (good s) bell) = 1/2 := by
  have hh := SupportProjection.mass_split (good s) bell
  have hv1 : mass (e := joint) bell = 1 := congrArg Complex.re normalized
  rw [omitted, hv1] at hh
  linarith

/-- The joint input really contains off-diagonal signal/environment coherence. -/
theorem input_coherence : (rank (e := joint) bell bell) (0,0) (1,1) = 1/2 := by
  norm_num [rank, Matrix.vecMulVec_apply, Pi.star_apply, bell, starRingEnd_apply, hadamardCoefficient_square]

/-- The good-support approximant changes the actual operator. -/
theorem ideal_cross_entry (s : Fin 2) :
    (SupportProjection.state (good s) bell (fallback s)).matrix (0,0) (1,1) = 0 := by
  have hs : good s (fallback s) := rfl
  by_cases h : s = 0
  · subst s
    have hh := SupportProjection.supported (a := joint) (good 0) bell (fallback 0) hs (1,1) (by decide)
    simp only [SupportProjection.state, PureProjection.pure, rank, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [hh, star_zero, mul_zero]
  · have h1 : s = 1 := by omega
    subst s
    have hh := SupportProjection.supported (a := joint) (good 1) bell (fallback 1) hs (0,0) (by decide)
    simp only [SupportProjection.state, PureProjection.pure, rank, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [hh, zero_mul]

def jointPredicate (i : (Guessing.publicSpace (Fin 2) joint).Basis) : Prop :=
  i.2.1 = (Fintype.equivFin (Fin 2)).symm i.1
instance : DecidablePred jointPredicate := fun _ => inferInstanceAs (Decidable (_ = _))

def measurement : Instrument (Guessing.publicSpace (Fin 2) joint) (Guessing.publicSpace (Fin 2) joint) 2 :=
  QuantumErrorTest.test jointPredicate

def channels : Nat → Channel (Guessing.publicSpace (Fin 2) joint) (Guessing.publicSpace (Fin 2) joint) :=
  fun _ => measurement.forget

/-- All operator premises are proved above, then the two-rule finite derivation
is interpreted. The public sample and entangled auxiliary qubit are retained. -/
theorem interpreted :
    (QuantumSamplingLogic.model distribution good bell normalized fallback channels).Carrier
      (.processed 0 (Real.sqrt (1/2))) := by
  apply QuantumSamplingLogic.sound distribution good bell normalized fallback channels
    (QuantumSamplingLogic.proof 0 (1/2))
  intro _
  exact classical

/-- Keeping the physical accept/reject record also preserves the same error
bound; the output contains that record, the public seed and both qubits. -/
theorem recorded :
    OperatorApprox (measurement.record.toKraus.apply (QuantumSampling.real distribution bell))
      (measurement.record.toKraus.apply (QuantumSampling.ideal distribution good bell fallback))
      (Real.sqrt (1/2)) :=
  (QuantumSampling.approximation distribution good bell normalized fallback (1/2) classical).postprocess measurement.record

/-- Even a branch with no good amplitude gets a normalized, supported ideal
state and a valid error bound; no zero probability is divided out. -/
theorem zero_good_branch :
    StateApprox (pure (SupportProjection.basisVector (a := joint) (0,0)) (SupportProjection.basis_unit _))
      (SupportProjection.state (good 1) (SupportProjection.basisVector (a := joint) (0,0)) (1,1)) 1 := by
  have hh := SupportProjection.approximation (good 1)
    (SupportProjection.basisVector (a := joint) (0,0)) (SupportProjection.basis_unit _) (1,1)
  convert hh using 1
  norm_num [mass, bracket, SupportProjection.drop, SupportProjection.basisVector, good,
    Fintype.sum_prod_type, Fin.sum_univ_two]

end
end Foundation.Quantum.QKD.QuantumSamplingExamples
