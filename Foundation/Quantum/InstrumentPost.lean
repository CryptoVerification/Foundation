import Foundation.Quantum.RecordObservation

/-! Physical postprocessing of every subnormalized instrument branch. -/
namespace Foundation.Quantum.Instrument
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b c : Space} {m : Nat}

def post (I : Instrument a b m) (C : Channel b c) : Instrument a c m where
  branch r := (I.branch r).seq C.toKraus
  complete := by
    simp only [Kraus.seq_effect]
    change (∑ r, (I.branch r).dual C.toKraus.effect) = 1
    rw [C.complete]
    simpa only [Kraus.dual_one] using I.complete

theorem post_apply (I : Instrument a b m) (C : Channel b c) (ρ : Operator a) (r : Fin m) :
    ((I.post C).branch r).apply ρ = C.toKraus.apply ((I.branch r).apply ρ) :=
  Kraus.seq_apply _ _ _

/-- Equality of every subnormalized branch implies equality of the full
physical record, without dividing by an outcome probability. -/
theorem record_congr (I J : Instrument a b m) (ρ : Operator a)
    (h : ∀ r, (I.branch r).apply ρ = (J.branch r).apply ρ) :
    I.record.toKraus.apply ρ = J.record.toKraus.apply ρ := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases hrs : r = s
  · subst s
    rw [record_diagonal, record_diagonal, h]
  · simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma, apply_ite, ite_mul, hrs]

end
end Foundation.Quantum.Instrument
