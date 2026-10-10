import Foundation.Quantum.WeightedObservation
import Foundation.Quantum.StateDistance
import Foundation.Quantum.QKD.SubnormalizedPhysical

/-! Observation bounds for actual operators, including subnormalized states.
Equal branch mass, rather than trace-one normalization, makes a difference
trace zero. The reconstruction witness contains algebraic data, not a desired
distance conclusion. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every binary physical observation of the operator difference is bounded. -/
def OperatorApprox {a : Space} (A B : Operator a) (ε : ℝ) : Prop :=
  ∀ E : Effect a, |(E.matrix*A).trace.re - (E.matrix*B).trace.re| ≤ ε

namespace OperatorApprox
variable {a b : Space} {A B C : Operator a} {ε δ : ℝ}

theorem refl (A : Operator a) : OperatorApprox A A 0 := by intro E; simp

theorem symm (h : OperatorApprox A B ε) : OperatorApprox B A ε := by
  intro E
  simpa only [abs_sub_comm] using h E

theorem trans (h : OperatorApprox A B ε) (g : OperatorApprox B C δ) : OperatorApprox A C (ε+δ) := by
  intro E
  exact (abs_sub_le _ _ _).trans (add_le_add (h E) (g E))

theorem postprocess (K : Channel a b) (h : OperatorApprox A B ε) :
    OperatorApprox (K.toKraus.apply A) (K.toKraus.apply B) ε := by
  intro E
  have hh := h (K.pullEffect E)
  change |(K.toKraus.dual E.matrix*A).trace.re - (K.toKraus.dual E.matrix*B).trace.re| ≤ ε at hh
  simpa only [K.toKraus.trace_dual] using hh

theorem weaken (h : OperatorApprox A B ε) (hεδ : ε ≤ δ) : OperatorApprox A B δ :=
  fun E => (h E).trans hεδ

theorem state_iff (ρ σ : Density a) : StateApprox ρ σ ε ↔ OperatorApprox ρ.matrix σ.matrix ε := Iff.rfl

/-- An explicit weighted square and reconstruction produce a real observation bound. -/
theorem of_factor (A B C D : Operator a) (hC : C.IsHermitian)
    (hrec : A-B = D.conjTranspose*C*D) (htrace : A.trace = B.trace) :
    OperatorApprox A B ((1/2:ℝ) * Real.sqrt
      (((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re * (C*C).trace.re)) := by
  have hz : (A-B).trace = 0 := by rw [Matrix.trace_sub, htrace, sub_self]
  intro E
  have h := weighted_observation (A-B) C D hC hrec hz E
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using h

end OperatorApprox

/-- Normalized states supply equal traces; the factor witness must still be constructed. -/
theorem stateApprox_of_factor {a : Space} (ρ σ : Density a) (C D : Operator a)
    (hC : C.IsHermitian) (hrec : ρ.matrix-σ.matrix = D.conjTranspose*C*D) :
    StateApprox ρ σ ((1/2:ℝ) * Real.sqrt
      (((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re * (C*C).trace.re)) :=
  OperatorApprox.of_factor _ _ C D hC hrec (ρ.normalized.trans σ.normalized.symm)

/-- Equal acceptance weight suffices for subnormalized CQ states. There is
no division by the mass, so the zero branch is included. -/
theorem subnormalizedApprox_of_factor {X : Type} [Fintype X] {e : Space}
    (ρ σ : QKD.Subnormalized.State X e) (C D : Operator (.tensor (.register (Fintype.card X)) e))
    (hC : C.IsHermitian) (hrec : QKD.Subnormalized.joint ρ-QKD.Subnormalized.joint σ = D.conjTranspose*C*D)
    (hmass : QKD.Subnormalized.mass ρ = QKD.Subnormalized.mass σ) :
    OperatorApprox (QKD.Subnormalized.joint ρ) (QKD.Subnormalized.joint σ) ((1/2:ℝ) * Real.sqrt
      (((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re * (C*C).trace.re)) :=
  OperatorApprox.of_factor _ _ C D hC hrec (by rw [QKD.Subnormalized.joint_trace_complex,
    QKD.Subnormalized.joint_trace_complex, hmass])

end
end Foundation.Quantum
