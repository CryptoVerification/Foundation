import Foundation.Quantum.PureProjection
import Foundation.Quantum.PublicMixtureObservation

/-! Actual normalized good-support approximants of finite pure states. The
zero-good-mass branch uses a specified unit basis vector inside the good set.
No conditional state is defined by dividing by a zero probability. -/
namespace Foundation.Quantum.SupportProjection
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false
variable {a : Space}

def keep (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) : a.Basis → ℂ :=
  fun i => if P i then v i else 0

def drop (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) : a.Basis → ℂ :=
  fun i => if P i then 0 else v i

theorem split (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) : keep P v+drop P v = v := by
  funext i
  by_cases hi : P i <;> simp [keep, drop, hi]

theorem orthogonal (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) :
    bracket (keep P v) (drop P v) = 0 ∧ bracket (drop P v) (keep P v) = 0 := by
  constructor <;> apply Finset.sum_eq_zero <;> intro i _ <;>
    by_cases hi : P i <;> simp [keep, drop, hi]

theorem mass_split (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) :
    mass (keep P v)+mass (drop P v) = mass v := by
  have hs := congrArg (fun u => bracket u u) (split P v)
  rw [bracket_add_left, bracket_add_right, bracket_add_right,
    (orthogonal P v).1, (orthogonal P v).2, add_zero, zero_add] at hs
  exact congrArg Complex.re hs

def basisVector (i : a.Basis) : a.Basis → ℂ := fun j => if j = i then 1 else 0

theorem basis_unit (i : a.Basis) : bracket (basisVector i) (basisVector i) = 1 := by
  simp [bracket, basisVector]

def vector (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) (i : a.Basis) : a.Basis → ℂ :=
  if 0 < mass (keep P v) then normalize (keep P v) else basisVector i

theorem vector_unit (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) (i : a.Basis) :
    bracket (vector P v i) (vector P v i) = 1 := by
  unfold vector
  split_ifs with h
  · exact normalize_unit _ h
  · exact basis_unit i

theorem supported (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ)
    (i : a.Basis) (hi : P i) (j : a.Basis) (hj : ¬ P j) : vector P v i j = 0 := by
  unfold vector
  split_ifs
  · simp [PureProjection.normalize, keep, hj]
  · have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [basisVector, hji]

def state (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ) (i : a.Basis) : Density a :=
  pure (vector P v i) (vector_unit P v i)

/-- Every binary quantum observation changes by at most the square root of the
omitted mass, including when the good component has exactly zero mass. -/
theorem approximation (P : a.Basis → Prop) [DecidablePred P] (v : a.Basis → ℂ)
    (hv : bracket v v = 1) (i : a.Basis) :
    StateApprox (pure v hv) (state P v i) (Real.sqrt (mass (drop P v))) := by
  have hv1 : mass v = 1 := by rw [mass, hv]; rfl
  have hm : mass (keep P v)+mass (drop P v) = 1 := (mass_split P v).trans hv1
  by_cases hg : 0 < mass (keep P v)
  · have hh := normalized_projection (keep P v) (drop P v) hg
      (orthogonal P v).1 (orthogonal P v).2 hm
    rw [split P v] at hh
    simpa only [OperatorApprox, StateApprox, Effect.probability, PureProjection.pure, state, vector, if_pos hg] using hh
  · have hg0 : mass (keep P v) = 0 := le_antisymm (le_of_not_gt hg) (mass_nonneg _)
    have hb1 : mass (drop P v) = 1 := by linarith
    rw [hb1, Real.sqrt_one]
    intro E
    apply abs_le.mpr
    constructor <;> linarith [E.probability_nonneg (pure v hv),
      E.probability_le_one (pure v hv), E.probability_nonneg (state P v i), E.probability_le_one (state P v i)]

end
end Foundation.Quantum.SupportProjection
