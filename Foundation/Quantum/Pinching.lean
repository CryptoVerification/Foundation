import Foundation.Quantum.HilbertChannelLogic
import Foundation.Quantum.InfiniteStates

/-! A nontrivial two-outcome pinching operation on infinite-dimensional states.
It deletes coherence between a unit vector and its orthogonal complement. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def unitProjection (x : E) : E →L[ℂ] E := InnerProductSpace.rankOne ℂ x x

@[simp] theorem unitProjection_adjoint (x : E) :
    (unitProjection x).adjoint = unitProjection x := InnerProductSpace.adjoint_rankOne x x

omit [CompleteSpace E] in
theorem unitProjection_comp (x : E) (hx : ‖x‖ = 1) :
    (unitProjection x).comp (unitProjection x) = unitProjection x := by
  simpa only [IsIdempotentElem, ContinuousLinearMap.mul_def, unitProjection] using
    InnerProductSpace.isIdempotentElem_rankOne_self (𝕜 := ℂ) hx

def pinching (x : E) (hx : ‖x‖ = 1) : HilbertChannel E E where
  index := Fin 2
  finite := inferInstance
  operator i := if i = 0 then unitProjection x else ContinuousLinearMap.id ℂ E - unitProjection x
  complete := by
    simp only [Fin.sum_univ_two, ↓reduceIte, Fin.isValue, (show (1 : Fin 2) ≠ 0 by decide),
      map_sub, ContinuousLinearMap.adjoint_id, unitProjection_adjoint,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, unitProjection_comp x hx]
    abel

/-- A concrete quantum operation on the full square-summable sequence space. -/
def coordinatePinching : HilbertChannel SequenceSpace SequenceSpace :=
  pinching (coordinateVector 0) (coordinateVector_norm 0)

/-- A genuine infinite-dimensional normalized input is accepted by the operation. -/
def pinchedGeometricDensity : TraceDensity SequenceSpace := coordinatePinching.run geometricDensity

/-- The coherence operator between coordinates 0 and 1 is nonzero before pinching. -/
def coordinateCoherence : TraceClass SequenceSpace :=
  TraceClass.ofSeries (NuclearSeries.single (coordinateVector 0) (coordinateVector 1))

theorem coordinateCoherence_apply :
    coordinateCoherence.operator (coordinateVector 1) = coordinateVector 0 := by
  simp [coordinateCoherence, TraceClass.ofSeries, NuclearSeries.single_operator, coordinateVector]

/-- Both alternatives remove the off-diagonal component. -/
theorem coordinatePinching_coherence : coordinatePinching.apply coordinateCoherence = 0 := by
  apply TraceClass.ext
  rw [HilbertChannel.operator_apply]
  simp only [coordinatePinching, pinching, Fin.sum_univ_two, ↓reduceIte, Fin.isValue, (show (1 : Fin 2) ≠ 0 by decide),
    TraceClass.operator_zero, coordinateCoherence, TraceClass.ofSeries, NuclearSeries.single_operator,
    map_sub, ContinuousLinearMap.adjoint_id, unitProjection_adjoint]
  simp only [unitProjection, InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]
  simp [coordinateVector, sub_apply, InnerProductSpace.rankOne_apply,
    lp.inner_single_left]

/-- A normalized superposition state; its two coordinates have nonzero coherence. -/
def coordinateSuperposition : TraceDensity SequenceSpace where
  state := (1 / 2 : ℂ) • TraceClass.ofSeries (NuclearSeries.single
    (coordinateVector 0 + coordinateVector 1) (coordinateVector 0 + coordinateVector 1))
  positive := by
    simp only [TraceClass.operator_smul, TraceClass.ofSeries, NuclearSeries.single_operator]
    exact (InnerProductSpace.isPositive_rankOne_self _).smul_of_nonneg (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by
    rw [TraceClass.trace_smul, TraceClass.trace_ofSeries, NuclearSeries.single_traceExpression]
    simp only [inner_add_left, inner_add_right]
    norm_num [coordinateVector, lp.inner_single_right]

theorem coordinateSuperposition_coherence :
    (coordinateSuperposition.state.operator (coordinateVector 1)) 0 = 1 / 2 := by
  simp [coordinateSuperposition, TraceClass.ofSeries, NuclearSeries.single_operator,
    coordinateVector, lp.inner_single_left, InnerProductSpace.rankOne_apply]

/-- Pinching removes the cross coefficient of every input, including mixed states. -/
theorem coordinatePinching_cross (T : TraceClass SequenceSpace) :
    ((coordinatePinching.apply T).operator (coordinateVector 1)) 0 = 0 := by
  rw [HilbertChannel.operator_apply]
  simp [coordinatePinching, pinching, Fin.sum_univ_two, unitProjection,
    InnerProductSpace.rankOne_apply, coordinateVector, lp.inner_single_left]

/-- This operation changes a normalized positive state on a genuinely infinite space. -/
theorem coordinatePinching_changes_state :
    (coordinatePinching.run coordinateSuperposition).state ≠ coordinateSuperposition.state := by
  intro h
  have he := congrArg (fun T : TraceClass SequenceSpace =>
    (T.operator (coordinateVector 1)) 0) h
  change ((coordinatePinching.apply coordinateSuperposition.state).operator (coordinateVector 1)) 0 =
    (coordinateSuperposition.state.operator (coordinateVector 1)) 0 at he
  rw [coordinatePinching_cross, coordinateSuperposition_coherence] at he
  norm_num at he

end
end Foundation.Quantum.Infinite
