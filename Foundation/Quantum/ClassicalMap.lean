import Foundation.Quantum.InstrumentMarginal

/-! Physical processing of a classical register with retained quantum data.
The map measures the input label and changes it deterministically. No quantum
coherence between different classical alternatives is silently merged. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- One Kraus operator for each classical input label. -/
def classicalMapOperator {n m : Nat} (a : Space) (f : Fin n → Fin m) (t : Fin n) :
    Op (.tensor (.register n) a) (.tensor (.register m) a) :=
  fun i j => if j.1 = t ∧ i.1 = f t ∧ i.2 = j.2 then 1 else 0

theorem classicalMap_complete {n m : Nat} (a : Space) (f : Fin n → Fin m) :
    (∑ t, (classicalMapOperator a f t).conjTranspose * classicalMapOperator a f t) = 1 := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp [classicalMapOperator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_and, mul_ite, eq_comm,
    Prod.mk.injEq, -Finset.sum_boole]
  split_ifs <;> simp_all

/-- A finite classical function becomes an actual trace-preserving quantum channel. -/
def classicalMap {n m : Nat} (a : Space) (f : Fin n → Fin m) :
    Channel (.tensor (.register n) a) (.tensor (.register m) a) where
  index := Fin n
  finite := inferInstance
  operator := classicalMapOperator a f
  complete := classicalMap_complete a f

/-- The entire conditional quantum state is preserved in each output alternative. -/
theorem classicalMap_apply {n m : Nat} (a : Space) (f : Fin n → Fin m)
    (ρ : Operator (.tensor (.register n) a)) (r s : Fin m) (i j : a.Basis) :
    (classicalMap a f).toKraus.apply ρ (r,i) (s,j) =
      if r = s then ∑ t : Fin n, if f t = r then ρ (t,i) (t,j) else 0 else 0 := by
  simp [classicalMap, Kraus.apply, classicalMapOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, ite_mul,
    eq_comm, apply_ite, -Finset.sum_boole]
  by_cases h : r = s
  · subst s
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl
  · simp [h]
    symm
    apply Finset.sum_eq_zero
    intro t _
    split_ifs <;> simp_all

/-- Discarding the relabelled register leaves the quantum marginal exactly unchanged. -/
theorem classicalMap_quantum_marginal {n m : Nat} (a : Space) (f : Fin n → Fin m)
    (ρ : Operator (.tensor (.register n) a)) (i j : a.Basis) :
    (∑ r : Fin m, (classicalMap a f).toKraus.apply ρ (r,i) (r,j)) =
      ∑ t : Fin n, ρ (t,i) (t,j) := by
  have h (r : Fin m) := classicalMap_apply a f ρ r r i j
  simp only [ite_true] at h
  simp_rw [h]
  rw [Finset.sum_comm]
  simp

end
end Foundation.Quantum
