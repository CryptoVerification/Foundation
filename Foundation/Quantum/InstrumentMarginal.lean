import Foundation.Quantum.InstrumentOps
import Foundation.Quantum.PartialTrace

/-! Local outcome probabilities agree with the reduced state, while the
instrument itself keeps the environment and its outcome correlations. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem discardRight_dual (a e : Space) (E : Operator a) :
    (discardRight a e).toKraus.dual E = Op.tensor E (Op.ident e) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [Kraus.dual, discardRight, traceOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.one_apply, ite_and, mul_ite, eq_comm, -Finset.sum_boole]
  by_cases h : u = v <;> simp [h, apply_ite]

namespace Instrument
variable {a b : Space} {n : Nat}

theorem amplify_probability (I : Instrument a b n) (e : Space)
    (ρ : Density (.tensor a e)) (r : Fin n) :
    (I.amplify e).probability ρ r = I.probability ((discardRight a e).run ρ) r := by
  unfold probability
  rw [branch_trace, branch_trace]
  change (((I.branch r).amplify e).effect * ρ.matrix).trace.re =
    ((I.branch r).effect * (discardRight a e).toKraus.apply ρ.matrix).trace.re
  rw [Kraus.amplify_effect]
  have h := congrArg Complex.re ((discardRight a e).toKraus.trace_dual ρ.matrix (I.branch r).effect)
  rw [discardRight_dual] at h
  exact h.symm

/-- The quantum marginal of a recorded channel is the instrument with its label forgotten. -/
theorem record_forget_marginal (I : Instrument a b n) (ρ : Operator a)
    (i j : b.Basis) :
    (∑ r : Fin n, I.record.toKraus.apply ρ (r,i) (r,j)) = I.forget.toKraus.apply ρ i j := by
  rw [I.forget_apply]
  simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_sigma, ite_mul]

end Instrument
end
end Foundation.Quantum
