import Foundation.Quantum.OperatorDistance

/-! Observation distance contracts under verified trace-nonincreasing Kraus
operations. The missing probability is not divided out. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
namespace Kraus
variable {a b : Space}

def pullSelective (K : Kraus a b) (hK : (1-K.effect).PosSemidef) (E : Effect b) : Effect a where
  matrix := K.dual E.matrix
  positive := K.dual_positive E.positive
  complement_positive := by
    have h := K.dual_positive E.complement_positive
    rw [dual_sub, dual_one] at h
    convert hK.add h using 1
    abel

end Kraus
namespace OperatorApprox
variable {a b : Space} {A B : Operator a} {ε : ℝ}

theorem selective (K : Kraus a b) (hK : (1-K.effect).PosSemidef) (h : OperatorApprox A B ε) :
    OperatorApprox (K.apply A) (K.apply B) ε := by
  intro E
  have hh := h (K.pullSelective hK E)
  change |(K.dual E.matrix*A).trace.re - (K.dual E.matrix*B).trace.re| ≤ ε at hh
  simpa only [K.trace_dual] using hh

end OperatorApprox
end
end Foundation.Quantum
