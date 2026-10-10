import Foundation.Quantum.QKD.HashLayout

/-! Classical processing of public data preserves the same uniform private
key comparator. The processing may forget information; it never reads the key. -/
namespace Foundation.Quantum.QKD.CommonKey
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {K L U : Type} [Fintype K] [Fintype L] [Fintype U]
  [Nonempty K] [DecidableEq K] [DecidableEq L] [DecidableEq U] {e : Space}

def publicProcess (ρ : State (K × L) e) (f : L → U) := relabel ρ (fun p => (p.1,f p.2))

omit [Nonempty K] [DecidableEq L] in
theorem publicProcess_block (ρ : State (K × L) e) (f : L → U) (k : K) (u : U) :
    (publicProcess ρ f).block (k,u) = ∑ l, if f l = u then ρ.block (k,l) else 0 := by
  simp [publicProcess, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

omit [DecidableEq L] in
theorem uniformize_publicProcess (ρ : State (K × L) e) (f : L → U) :
    publicProcess (uniformize ρ) f = uniformize (publicProcess ρ f) := by
  apply State.ext
  funext ⟨k,u⟩
  rw [publicProcess_block]
  change (∑ l, if f l = u then ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k', ρ.block (k',l) else 0) =
    ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k', (publicProcess ρ f).block (k',u)
  simp_rw [publicProcess_block]
  rw [Finset.sum_comm]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : f l = u <;> simp [hl]

omit [DecidableEq L] in
theorem publicProcess_secrecy (ρ : State (K × L) e) (f : L → U) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint (uniformize ρ)) ε) :
    OperatorApprox (joint (publicProcess ρ f)) (joint (uniformize (publicProcess ρ f))) ε := by
  have hh := h.postprocess (classicalMap e (fun t => Fintype.equivFin (K × U)
    (let p := (Fintype.equivFin (K × L)).symm t; (p.1,f p.2))))
  rw [← relabel_physical ρ (fun p => (p.1,f p.2)),
    ← relabel_physical (uniformize ρ) (fun p => (p.1,f p.2))] at hh
  change OperatorApprox (joint (publicProcess ρ f)) (joint (publicProcess (uniformize ρ) f)) ε at hh
  rw [uniformize_publicProcess] at hh
  exact hh

end
end Foundation.Quantum.QKD.CommonKey
