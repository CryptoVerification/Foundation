import Foundation.Quantum.RecordObservation

/-! Physical measurement records commute with implementing their channel
preprocessing, also with arbitrary retained auxiliary entanglement. -/
namespace Foundation.Quantum.Instrument
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b c : Space} {m : Nat}

theorem amplify_record_pre_apply (I : Instrument b c m) (C : Channel a b) (e : Space)
    (ρ : Operator (.tensor a e)) :
    ((I.pre C).amplify e).record.toKraus.apply ρ =
      (I.amplify e).record.toKraus.apply ((C.amplify e).toKraus.apply ρ) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · subst s
    rw [record_diagonal, record_diagonal, amplify_pre_apply]
  · simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma, apply_ite, ite_mul, h]

end
end Foundation.Quantum.Instrument
