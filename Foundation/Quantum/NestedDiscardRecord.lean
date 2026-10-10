import Foundation.Quantum.NestedDiscard
import Foundation.Quantum.RetainedControl
import Foundation.Quantum.PartitionDelay

/-! Retaining a detailed measurement outcome commutes with tracing out only
the newly added environment. The outcome and all other systems are retained. -/
namespace Foundation.Quantum.NestedDiscard
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem record {a b e r : Space} {m : Nat} (f : a.Basis → Fin m)
    (ρ : Operator (.tensor a (.tensor b (.tensor e r)))) :
    (RetainedControl.channel (fun _ : Fin m => channel a b e r)).toKraus.apply
      ((PartitionMeasurement.instrument (fun p : (Space.tensor a (.tensor b (.tensor e r))).Basis =>
        f p.1)).record.toKraus.apply ρ) =
      (PartitionMeasurement.instrument (fun p : (Space.tensor a (.tensor b e)).Basis =>
        f p.1)).record.toKraus.apply ((channel a b e r).toKraus.apply ρ) := by
  ext ⟨s,i,u,x⟩ ⟨t,j,v,y⟩
  rw [RetainedControl.apply_entry, PartitionMeasurement.record_entry]
  by_cases h : s = t
  · subst t
    simp only [ite_true, true_and]
    rw [apply_entry]
    change (∑ z : r.Basis,
      (PartitionMeasurement.instrument (fun p : (Space.tensor a (.tensor b (.tensor e r))).Basis =>
        f p.1)).record.toKraus.apply ρ (s,(i,(u,(x,z)))) (s,(j,(v,(y,z))))) = _
    have he (z : r.Basis) := PartitionMeasurement.record_entry
      (fun p : (Space.tensor a (.tensor b (.tensor e r))).Basis => f p.1) ρ
      s s (i,(u,(x,z))) (j,(v,(y,z)))
    apply Eq.trans (Finset.sum_congr rfl (fun z _ => he z))
    simp only [true_and]
    by_cases hh : f i = s ∧ f j = s
    · simp only [hh, and_self, ite_true]
      exact (apply_entry a b e r ρ i j u v x y).symm
    · simp only [hh, ite_false, Finset.sum_const_zero]
  · simp only [h, false_and, ite_false]

end
end Foundation.Quantum.NestedDiscard
