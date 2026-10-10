import Foundation.Quantum.NestedDiscardRecord
import Foundation.Quantum.PartitionDiscard

/-! Tracing only the last auxiliary environment commutes with complete
classical records and deterministic classical processing. -/
namespace Foundation.Quantum.NestedDiscard
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem discard_signal {a b e r : Space} {m : Nat} (f : a.Basis → Fin m)
    (ρ : Operator (.tensor a (.tensor b (.tensor e r)))) :
    (channel (.register m) b e r).toKraus.apply
      ((PartitionMeasurement.discardSignal f (.tensor b (.tensor e r))).toKraus.apply ρ) =
      (PartitionMeasurement.discardSignal f (.tensor b e)).toKraus.apply
        ((channel a b e r).toKraus.apply ρ) := by
  ext ⟨i,u,x⟩ ⟨j,v,y⟩
  rw [apply_entry]
  have hl (t : r.Basis) := PartitionMeasurement.discard_entry (a := a)
    (e := .tensor b (.tensor e r)) f ρ i j (u,(x,t)) (v,(y,t))
  have hr := PartitionMeasurement.discard_entry (a := a) (e := .tensor b e)
    f ((channel a b e r).toKraus.apply ρ) i j (u,x) (v,y)
  rw [hr]
  simp_rw [hl]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [apply_entry]
    by_cases hz : f z = i <;> simp only [hz, ite_true, ite_false, Finset.sum_const_zero]
  · simp only [hij, ite_false, Finset.sum_const_zero]

theorem classical_map {b e r : Space} {m k : Nat} (f : Fin m → Fin k)
    (ρ : Operator (.tensor (.register m) (.tensor b (.tensor e r)))) :
    (channel (.register k) b e r).toKraus.apply
      ((classicalMap (.tensor b (.tensor e r)) f).toKraus.apply ρ) =
      (classicalMap (.tensor b e) f).toKraus.apply
        ((channel (.register m) b e r).toKraus.apply ρ) := by
  ext ⟨i,u,x⟩ ⟨j,v,y⟩
  rw [apply_entry]
  have hl (t : r.Basis) := classicalMap_apply (.tensor b (.tensor e r)) f ρ
    i j (u,(x,t)) (v,(y,t))
  have hr := classicalMap_apply (.tensor b e) f ((channel (.register m) b e r).toKraus.apply ρ)
    i j (u,x) (v,y)
  rw [hr]
  simp_rw [hl]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [apply_entry]
    by_cases hz : f z = i <;> simp only [hz, ite_true, ite_false, Finset.sum_const_zero]
  · simp only [hij, ite_false, Finset.sum_const_zero]

end
end Foundation.Quantum.NestedDiscard
