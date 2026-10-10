import Foundation.Quantum.QKD.BB84KeyState
import Foundation.Quantum.Mixture

/-! Physical finite classical control. The input label is measured, and its
selected channel acts on the whole remaining quantum system. Coherence inside
that system is retained; coherence between classical alternatives is discarded. -/
namespace Foundation.Quantum.ClassicalControl
noncomputable section
set_option backward.isDefEq.respectTransparency false

def select {m : Nat} (a : Space) (t : Fin m) : Op (.tensor (.register m) a) a :=
  fun i j => if j.1 = t ∧ i = j.2 then 1 else 0

theorem select_complete {m : Nat} (a : Space) :
    (∑ t : Fin m, (select a t).conjTranspose * select a t) = 1 := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp [select, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, ite_and, mul_ite, eq_comm, Prod.mk.injEq, -Finset.sum_boole]
  split_ifs <;> simp_all

def channel {m : Nat} {a b : Space} (C : Fin m → Channel a b) :
    Channel (.tensor (.register m) a) b where
  index := (t : Fin m) × (C t).index
  finite := inferInstance
  operator p := (C p.1).operator p.2 * select a p.1
  complete := by
    change (∑ p : (t : Fin m) × (C t).index,
      ((C p.1).operator p.2 * select a p.1).conjTranspose *
        ((C p.1).operator p.2 * select a p.1)) = 1
    simp only [Fintype.sum_sigma, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    have inner (t : Fin m) :
        (∑ k, (select a t).conjTranspose *
          ((C t).operator k).conjTranspose * ((C t).operator k * select a t)) =
        (select a t).conjTranspose * select a t := by
      simp only [← Matrix.mul_assoc]
      rw [← Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_sum]
      change ((select a t).conjTranspose * (C t).toKraus.effect) * select a t = _
      rw [(C t).complete, Matrix.mul_one]
    simp_rw [← Matrix.mul_assoc (select a _).conjTranspose, inner]
    exact select_complete a

theorem select_block {m : Nat} (a : Space) (t : Fin m)
    (ρ : Operator (.tensor (.register m) a)) :
    select a t * ρ * (select a t).conjTranspose =
      fun i j => ρ (t,i) (t,j) := by
  ext i j
  simp [select, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    ite_and, ite_mul, apply_ite, eq_comm]

theorem apply {m : Nat} {a b : Space} (C : Fin m → Channel a b)
    (ρ : Operator (.tensor (.register m) a)) :
    (channel C).toKraus.apply ρ =
      ∑ t, (C t).toKraus.apply (fun i j => ρ (t,i) (t,j)) := by
  simp only [channel, Kraus.apply, Fintype.sum_sigma, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  rw [← select_block a t ρ]
  simp only [Matrix.mul_assoc]

theorem basis {m : Nat} {a b : Space} (C : Fin m → Channel a b)
    (t : Fin m) (ρ : Density a) :
    ((channel C).run (QKD.tensorDensity (basisDensity (.register m) t) ρ)).matrix =
      ((C t).run ρ).matrix := by
  rw [show ((channel C).run _).matrix = (channel C).toKraus.apply _ from rfl, apply]
  have block (s : Fin m) :
      (fun i j => (QKD.tensorDensity (basisDensity (.register m) t) ρ).matrix (s,i) (s,j)) =
      if s = t then ρ.matrix else 0 := by
    ext i j
    by_cases h : s = t <;> simp [h, QKD.tensorDensity, basisDensity, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.diagonal_apply, Matrix.of_apply]
  simp_rw [block]
  have zero (s : Fin m) : (C s).toKraus.apply 0 = 0 := (C s).toKraus.linear.map_zero
  simp only [apply_ite, zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

end
end Foundation.Quantum.ClassicalControl
