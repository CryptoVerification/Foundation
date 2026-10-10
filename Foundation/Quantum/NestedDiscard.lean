import Foundation.Quantum.PartialTrace
import Foundation.Quantum.BasisChannel

/-! Trace out only the last environment in a nested tensor, retaining the
signal, a second quantum subsystem, and the original adversary's system. -/
namespace Foundation.Quantum.NestedDiscard
noncomputable section
set_option backward.isDefEq.respectTransparency false

def rearrange (a b e r : Space) :
    (Space.tensor a (.tensor b (.tensor e r))).Basis ≃
      (Space.tensor (.tensor a (.tensor b e)) r).Basis where
  toFun p := ((p.1,(p.2.1,p.2.2.1)),p.2.2.2)
  invFun p := (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def channel (a b e r : Space) :
    Channel (.tensor a (.tensor b (.tensor e r))) (.tensor a (.tensor b e)) :=
  (BasisChannel.channel (rearrange a b e r)).seq (discardRight (.tensor a (.tensor b e)) r)

theorem apply_entry (a b e r : Space) (ρ : Operator (.tensor a (.tensor b (.tensor e r))))
    (i j : a.Basis) (u v : b.Basis) (x y : e.Basis) :
    (channel a b e r).toKraus.apply ρ (i,(u,x)) (j,(v,y)) =
      ∑ t : r.Basis, ρ (i,(u,(x,t))) (j,(v,(y,t))) := by
  change ((BasisChannel.channel (rearrange a b e r)).toKraus.seq
    (discardRight (.tensor a (.tensor b e)) r).toKraus).apply ρ _ _ = _
  rw [Kraus.seq_apply, discardRight_apply, BasisChannel.apply]
  rfl

/-- Naturality for an arbitrary channel on the signal, including entangled
input and a nontrivial retained subsystem. No product-state premise is used. -/
theorem local_operations {a c : Space} (C : Channel a c) (b e r : Space)
    (ρ : Operator (.tensor a (.tensor b (.tensor e r)))) :
    (channel c b e r).toKraus.apply
      ((C.amplify (.tensor b (.tensor e r))).toKraus.apply ρ) =
      (C.amplify (.tensor b e)).toKraus.apply ((channel a b e r).toKraus.apply ρ) := by
  ext ⟨i,u,x⟩ ⟨j,v,y⟩
  rw [apply_entry]
  change (∑ t : r.Basis, (C.toKraus.amplify (.tensor b (.tensor e r))).apply ρ
      (i,(u,(x,t))) (j,(v,(y,t)))) =
    (C.toKraus.amplify (.tensor b e)).apply ((channel a b e r).toKraus.apply ρ) (i,(u,x)) (j,(v,y))
  have hl (t : r.Basis) := Kraus.amplify_apply_entry C.toKraus (.tensor b (.tensor e r)) ρ
    i j (u,(x,t)) (v,(y,t))
  have hr := Kraus.amplify_apply_entry C.toKraus (.tensor b e)
    ((channel a b e r).toKraus.apply ρ) i j (u,x) (v,y)
  apply Eq.trans (Finset.sum_congr rfl (fun t _ => hl t))
  apply Eq.trans _ hr.symm
  calc
    _ = ∑ k, ∑ s : a.Basis, ∑ z : a.Basis, ∑ t : r.Basis,
        C.operator k i s * ρ (s,(u,(x,t))) (z,(v,(y,t))) * star (C.operator k j z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_mul, ← Finset.mul_sum, apply_entry]

end
end Foundation.Quantum.NestedDiscard
