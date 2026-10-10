import Foundation.Quantum.ClassicalControl
import Foundation.Quantum.PublicMixtureObservation

/-! Physical classical control that retains the controlling public label.
The controlled channel may act on an arbitrarily entangled quantum input. -/
namespace Foundation.Quantum.RetainedControl
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b : Space} {m : Nat}

def tag (t : Fin m) : Channel b (.tensor (.register m) b) :=
  Channel.ofIsometry (Instrument.recordOperator t (Op.ident b)) (by
    rw [Instrument.recordOperator_gram]
    simp [Op.ident])

theorem tag_entry (t : Fin m) (ρ : Operator b) (r s : Fin m) (i j : b.Basis) :
    (tag t).toKraus.apply ρ (r,i) (s,j) = if r = t ∧ s = t then ρ i j else 0 := by
  change (Kraus.single (Instrument.recordOperator t (Op.ident b))).apply ρ _ _ = _
  rw [Kraus.single_apply]
  simp [Instrument.recordOperator, Op.ident, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, ite_and, ite_mul, apply_ite, eq_comm]
  by_cases hr : r = t <;> by_cases hs : s = t <;> simp_all [eq_comm]

def channel (C : Fin m → Channel a b) :
    Channel (.tensor (.register m) a) (.tensor (.register m) b) :=
  ClassicalControl.channel (fun t => (C t).seq (tag t))

theorem apply_entry (C : Fin m → Channel a b) (ρ : Operator (.tensor (.register m) a))
    (r s : Fin m) (i j : b.Basis) :
    (channel C).toKraus.apply ρ (r,i) (s,j) =
      if r = s then (C r).toKraus.apply (Matrix.of (fun u v => ρ (r,u) (r,v))) i j else 0 := by
  rw [channel, ClassicalControl.apply]
  change (∑ t, ((C t).seq (tag t)).toKraus.apply
    (Matrix.of (fun u v => ρ (t,u) (t,v)))) (r,i) (s,j) = _
  simp only [Channel.seq, Kraus.seq_apply]
  have he : (∑ t : Fin m, (tag t).toKraus.apply
      ((C t).toKraus.apply (Matrix.of (fun u v => ρ (t,u) (t,v))))) (r,i) (s,j) =
      ∑ t : Fin m, if r = t ∧ s = t then
        (C t).toKraus.apply (Matrix.of (fun u v => ρ (t,u) (t,v))) i j else 0 := by
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    exact tag_entry t _ r s i j
  rw [he]
  by_cases h : r = s
  · subst s
    simp only [and_self, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · have hh (t : Fin m) : ¬ (r = t ∧ s = t) := fun ht => h (ht.1.trans ht.2.symm)
    simp only [hh, h, ite_false, Finset.sum_const_zero]

/-- Full joint equality with the public label retained, not only a quantum
marginal or a classical probability law. Operators need not be normalized. -/
theorem public_apply {S : Type} [Fintype S] [DecidableEq S] (p : PMF S)
    (C : Fin (Fintype.card S) → Channel a b) (A : S → Operator a) :
    (channel C).toKraus.apply (publicMixture p A) =
      publicMixture p (fun s => (C (Fintype.equivFin S s)).toKraus.apply (A s)) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin S).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin S).surjective s
  rw [apply_entry, publicMixture_block]
  simp only [(Fintype.equivFin S).injective.eq_iff]
  by_cases h : x = y
  · subst y
    simp only [ite_true]
    have hb : Matrix.of (fun u v => publicMixture p A
        (Fintype.equivFin S x,u) (Fintype.equivFin S x,v)) = ((p x).toReal : ℂ) • A x := by
      ext u v
      change publicMixture p A (Fintype.equivFin S x,u) (Fintype.equivFin S x,v) = _
      rw [publicMixture_block]
      simp only [ite_true, Matrix.smul_apply, smul_eq_mul]
    rw [hb]
    exact congrArg (fun τ => τ i j) ((C (Fintype.equivFin S x)).toKraus.linear.map_smul _ _)
  · simp only [h, ite_false]

end
end Foundation.Quantum.RetainedControl
