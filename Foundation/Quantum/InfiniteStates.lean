import Foundation.Quantum.TraceClass
import Foundation.Quantum.GeometricOperator

/-! A genuinely infinite diagonal state with representation-independent trace.
Trace-norm completion and arbitrary normal channels remain separate obligations. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder

theorem geometricOperator_positive : geometricSeries.operator.IsPositive := by
  apply geometricSeries.operator_positive
  intro n
  change (InnerProductSpace.rankOne ℂ (((1 / 2 : ℂ) ^ n / 2) • coordinateVector n)
    (coordinateVector n)).IsPositive
  rw [map_smul]
  apply (InnerProductSpace.isPositive_rankOne_self (coordinateVector n)).smul_of_nonneg
  positivity

/-- A normalized mixed state on the full sequence Hilbert space. -/
def geometricDensity : TraceDensity SequenceSpace where
  state := TraceClass.ofSeries geometricSeries
  positive := geometricOperator_positive
  normalized := by rw [TraceClass.trace_ofSeries, geometricSeries_trace]

theorem geometricDensity_coordinate (n : ℕ) :
    geometricDensity.state.operator (coordinateVector n) =
      ((1 / 2 : ℂ) ^ n / 2) • coordinateVector n := geometricOperator_coordinate n

end
end Foundation.Quantum.Infinite
