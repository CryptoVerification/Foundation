import Foundation.Quantum.TraceIdealNorm
import Foundation.Quantum.TraceCompleteness
import Foundation.Quantum.HilbertChannel
import Foundation.Quantum.Pinching

/-! Concrete quantum operations on arbitrary Hilbert spaces act continuously
on the complete nuclear ideal. The finite-Kraus norm bound below is a valid
bound, not a claim of the optimal trace-distance contraction theorem. -/
namespace Foundation.Quantum.Infinite.HilbertChannel
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def linear (K : HilbertChannel E F) : TraceClass E →ₗ[ℂ] TraceClass F :=
  ∑ i, (TraceClass.conjugateContinuous (K.operator i)).toLinearMap

theorem linear_apply (K : HilbertChannel E F) (T : TraceClass E) : K.linear T = K.apply T := by
  simp only [linear, LinearMap.sum_apply]
  rfl

theorem norm_apply_le (K : HilbertChannel E F) (T : TraceClass E) :
    ‖K.apply T‖ ≤ (∑ i, ‖K.operator i‖^2) * ‖T‖ := by
  calc
    _ ≤ ∑ i, ‖T.conjugate (K.operator i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖K.operator i‖^2 * ‖T‖ :=
      Finset.sum_le_sum (fun i _ => T.norm_conjugate_le (K.operator i))
    _ = _ := (Finset.sum_mul _ _ _).symm

def continuous (K : HilbertChannel E F) : TraceClass E →L[ℂ] TraceClass F :=
  K.linear.mkContinuous (∑ i, ‖K.operator i‖^2) (fun T => by rw [linear_apply]; exact K.norm_apply_le T)

@[simp] theorem continuous_apply (K : HilbertChannel E F) (T : TraceClass E) :
    K.continuous T = K.apply T := K.linear_apply T

theorem trace_continuous (K : HilbertChannel E F) (T : TraceClass E) :
    TraceClass.traceContinuous (K.continuous T) = TraceClass.traceContinuous T := by
  change (K.continuous T).trace = T.trace
  rw [continuous_apply]
  exact K.trace_apply T

/-- The concrete operation is continuous and still removes actual nonzero coherence. -/
theorem coordinatePinching_continuous_coherence : coordinatePinching.continuous coordinateCoherence = 0 := by
  rw [continuous_apply]
  exact coordinatePinching_coherence

end
end Foundation.Quantum.Infinite.HilbertChannel
