import Foundation.Quantum.QKD.PublicKeyProcess
import Foundation.Quantum.QKD.SubnormalizedProcessing

/-! Quantum processing preserves the same uniform private-key comparator.
Selection and public hashing commute with a channel acting only on the side system. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Subnormalized
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {a b : Space}

theorem post_ofCQ (ρ : Guessing.CQ X a) (C : Channel a b) :
    post (ofCQ ρ) C = ofCQ (Guessing.post ρ C) := rfl

theorem post_restrict (ρ : State X a) (C : Channel a b) (P : X → Prop) [DecidablePred P] :
    post (restrict ρ P) C = restrict (post ρ C) P := by
  apply State.ext
  funext x
  by_cases h : P x
  · simp only [post, restrict, h, ite_true]
  · simp only [post, restrict, h, ite_false]
    exact C.toKraus.linear.map_zero

theorem post_relabel [DecidableEq Y] (ρ : State X a) (C : Channel a b) (f : X → Y) :
    post (relabel ρ f) C = relabel (post ρ C) f := by
  apply State.ext
  funext y
  change C.toKraus.linear (∑ x, if f x = y then ρ.block x else 0) =
    ∑ x, if f x = y then C.toKraus.linear (ρ.block x) else 0
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y <;> simp [h]

theorem post_seed (ρ : State X a) (C : Channel a b) (p : PMF S) :
    post (seed p ρ) C = seed p (post ρ C) := by
  apply State.ext
  funext sx
  exact C.toKraus.linear.map_smul _ _

end Subnormalized

namespace CommonKey
open Subnormalized
variable {K T : Type} [Fintype K] [Nonempty K] [Fintype T] {a b : Space}

theorem uniformize_post (ρ : State (K × T) a) (C : Channel a b) :
    post (uniformize ρ) C = uniformize (post ρ C) := by
  apply State.ext
  funext p
  change C.toKraus.linear (((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, ρ.block (k,p.2)) =
    ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, C.toKraus.linear (ρ.block (k,p.2))
  rw [map_smul, map_sum]

theorem quantumProcess_secrecy [DecidableEq K] [DecidableEq T]
    (ρ : State (K × T) a) (C : Channel a b) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint (uniformize ρ)) ε) :
    OperatorApprox (joint (post ρ C)) (joint (uniformize (post ρ C))) ε := by
  have hh := h.postprocess (rightChannel (.register (Fintype.card (K × T))) C)
  rw [← post_physical ρ C, ← post_physical (uniformize ρ) C, uniformize_post] at hh
  exact hh

end CommonKey
end
end Foundation.Quantum.QKD
