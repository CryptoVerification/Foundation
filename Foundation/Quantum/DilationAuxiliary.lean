import Foundation.Quantum.Dilation
import Foundation.Quantum.SourceReplacement

/-! Finite channel dilation with an arbitrary retained auxiliary system.
This permits coherent-source proofs without assuming that an arbitrary Kraus
attack has pure output. Discarding only its new environment recovers the
original joint state, including all auxiliary correlations. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem discardRight_amplify_apply (a e r : Space)
    (ρ : Operator (.tensor (.tensor a e) r))
    (i j : a.Basis) (u v : r.Basis) :
    ((discardRight a e).amplify r).toKraus.apply ρ (i,u) (j,v) =
      ∑ k : e.Basis, ρ ((i,k),u) ((j,k),v) := by
  change ((discardRight a e).toKraus.amplify r).apply ρ (i,u) (j,v) = _
  rw [Kraus.amplify_apply_entry]
  simp [discardRight, traceOperator, Fintype.sum_prod_type, ite_and, ite_mul,
    apply_ite]

namespace Channel
variable {a b : Space}

/-- The Stinespring environment can be discarded while an arbitrary other
system remains present. The input need not be a product state. -/
theorem discard_dilation_amplify (C : Channel a b) (r : Space)
    (ρ : Operator (.tensor a r)) :
    ((discardRight b (.register (Fintype.card C.index))).amplify r).toKraus.apply
      ((C.dilated.amplify r).toKraus.apply ρ) = (C.amplify r).toKraus.apply ρ := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [discardRight_amplify_apply]
  change (∑ k, (C.dilated.toKraus.amplify r).apply ρ ((i,k),u) ((j,k),v)) =
    (C.toKraus.amplify r).apply ρ (i,u) (j,v)
  rw [Kraus.amplify_apply_entry C.toKraus r ρ i j u v]
  have entry (k : Fin (Fintype.card C.index)) :=
    Kraus.amplify_apply_entry C.dilated.toKraus r ρ (i,k) (j,k) u v
  simp_rw [entry]
  simp only [dilated, Channel.ofIsometry, Kraus.single, Fintype.sum_unique, dilation]
  exact Equiv.sum_comp (Fintype.equivFin C.index).symm
    (fun k => ∑ s : a.Basis, ∑ t : a.Basis,
      C.operator k i s * ρ (s,u) (t,v) * star (C.operator k j t))

def pureDilationVector (C : Channel a b) (r : Space) (v : (Space.tensor a r).Basis → ℂ) :
    (Space.tensor (.tensor b (.register (Fintype.card C.index))) r).Basis → ℂ :=
  (Op.tensor C.dilation (Op.ident r)).mulVec v

theorem pure_dilation (C : Channel a b) (r : Space) (v : (Space.tensor a r).Basis → ℂ) :
    (C.dilated.amplify r).toKraus.apply (PureProjection.rank v v) =
      PureProjection.rank (C.pureDilationVector r v) (C.pureDilationVector r v) := by
  change (Kraus.single (Op.tensor C.dilation (Op.ident r))).apply (PureProjection.rank v v) = _
  rw [Kraus.single_apply]
  exact SourceReplacement.rank_conjugate _ v

theorem pure_dilation_unit (C : Channel a b) (r : Space) (v : (Space.tensor a r).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) :
    PureProjection.bracket (C.pureDilationVector r v) (C.pureDilationVector r v) = 1 := by
  let ρ : Density (.tensor a r) :=
    ⟨PureProjection.rank v v, QKD.CoherentSupport.outer_positive v, by rw [PureProjection.rank_trace]; exact hv⟩
  have h := ((C.dilated.amplify r).run ρ).normalized
  change ((C.dilated.amplify r).toKraus.apply (PureProjection.rank v v)).trace = 1 at h
  rw [pure_dilation, PureProjection.rank_trace] at h
  exact h

end Channel
end
end Foundation.Quantum
