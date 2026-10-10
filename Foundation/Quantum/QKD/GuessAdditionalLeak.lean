import Foundation.Quantum.QKD.GuessPublic
import Foundation.Quantum.QKD.GuessLogic

/-! Additional finite public communication costs only its own alphabet size,
with all previously public information already included in the side system.
This is the interface for a verified reconciliation transcript; it does not
assert any reconciliation algorithm or bound its actual message length. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X C L : Type} [Fintype X] [Fintype C] [Fintype L] {e : Space}

/-- Remove only the newly disclosed message C, retaining the old public L. -/
def forgetMessage (ρ : CQ ((X × C) × L) e) : CQ (X × L) e where
  block p := ∑ c, ρ.block ((p.1,c),p.2)
  positive p := Matrix.posSemidef_sum _ (fun c _ => ρ.positive ((p.1,c),p.2))
  normalized := by
    simp only [Matrix.trace_sum, Fintype.sum_prod_type]
    have h := ρ.normalized
    simp only [Fintype.sum_prod_type] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]

/-- The new-message marginal agrees with retaining the old public register first. -/
theorem hide_withPublic (ρ : CQ ((X × C) × L) e) :
    hideLeak (withPublic ρ) = withPublic (forgetMessage ρ) := by
  apply CQ.ext
  funext x
  ext ⟨r,i⟩ ⟨s,j⟩
  simp only [hideLeak, withPublic, forgetMessage, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A second public message has a multiplicative cost |C|, relative to
optimal guessing with the entire previous public transcript L and quantum E. -/
theorem additional_leakage (ρ : CQ ((X × C) × L) e) :
    leakedGuessingProbability (withPublic ρ) ≤
      Fintype.card C * leakedGuessingProbability (forgetMessage ρ) := by
  have h := leakage_chain (withPublic ρ)
  rw [hide_withPublic, withPublic_optimal] at h
  exact h

/-- Additional public communication as a real deterministic classical process.
The message may depend on both the private input and the old transcript. -/
def disclose [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : CQ (X × L) e) (message : X → L → C) : CQ ((X × C) × L) e :=
  relabel ρ (fun p => ((p.1,message p.1 p.2),p.2))

theorem forget_disclose [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : CQ (X × L) e) (message : X → L → C) : forgetMessage (disclose ρ message) = ρ := by
  apply CQ.ext
  funext ⟨x,l⟩
  simp only [forgetMessage, disclose, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp
  rw [Finset.sum_comm]
  simp

theorem disclosure_cost [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : CQ (X × L) e) (message : X → L → C) :
    leakedGuessingProbability (withPublic (disclose ρ message)) ≤
      Fintype.card C * leakedGuessingProbability ρ := by
  simpa only [forget_disclose] using additional_leakage (disclose ρ message)

/-- The same bound is a composite derivation in the existing logic. Its
operator certificate concerns the state with all old public data retained. -/
theorem additional_interpreted (ρ : CQ ((X × C) × L) e)
    (σ : Density (publicSpace L e)) (q : ℝ)
    (h : Dominated (withPublic (forgetMessage ρ)) σ q) :
    leakedGuessingProbability (withPublic ρ) ≤ Fintype.card C * q := by
  apply GuessLogic.sound (fun _ => withPublic ρ) (fun _ => σ)
    (GuessLogic.leakProof (Fintype.card C) 0 0 q)
  intro _
  change Dominated (hideLeak (withPublic ρ)) σ q
  simpa only [hide_withPublic] using h

end
end Foundation.Quantum.QKD.Guessing
