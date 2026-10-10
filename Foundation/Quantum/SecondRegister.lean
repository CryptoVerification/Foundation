import Foundation.Quantum.QKD.CQRepresentation
import Foundation.Quantum.SourceReplacement

/-! Measuring the second subsystem into a classical register while retaining
the entire first subsystem. The channel is constructed with explicit Kraus
operators, and its full CQ density is identified entry by entry. -/
namespace Foundation.Quantum.SecondRegister
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

def operator (a b : Space) (x : a.Basis) : Op (.tensor b a) (.tensor (.register (Fintype.card a.Basis)) b) :=
  fun i j => if i.1 = Fintype.equivFin a.Basis x ∧ i.2 = j.1 ∧ j.2 = x then 1 else 0

theorem complete (a b : Space) :
    (∑ x, (operator a b x).conjTranspose * operator a b x) = (1 : Operator (.tensor b a)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [operator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, apply_ite, eq_comm,
    -Finset.sum_boole]
  by_cases hi : i = j <;> by_cases hx : x = y <;> simp_all

def channel (a b : Space) : Channel (.tensor b a) (.tensor (.register (Fintype.card a.Basis)) b) where
  index := a.Basis
  finite := inferInstance
  operator := operator a b
  complete := complete a b

theorem apply_entry (a b : Space) (ρ : Operator (.tensor b a)) (x y : a.Basis) (i j : b.Basis) :
    (channel a b).toKraus.apply ρ (Fintype.equivFin a.Basis x,i) (Fintype.equivFin a.Basis y,j) =
      if x = y then ρ (i,x) (j,x) else 0 := by
  simp [channel, Kraus.apply, operator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, ite_mul,
    apply_ite, -Finset.sum_boole]
  by_cases h : x = y <;> simp_all

def cq (ρ : Density (.tensor b a)) : QKD.Guessing.CQ a.Basis b where
  block x := SourceReplacement.slice ρ.matrix x
  positive x := ρ.positive.submatrix (fun i => (i,x))
  normalized := by
    change (∑ x : a.Basis, ∑ i : b.Basis, ρ.matrix (i,x) (i,x)) = 1
    rw [Finset.sum_comm]
    simpa only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using ρ.normalized

/-- The abstract CQ record is the actual measurement channel's joint output. -/
theorem physical (ρ : Density (.tensor b a)) :
    ((channel a b).run ρ).matrix = (cq ρ).density.matrix := by
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin a.Basis).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin a.Basis).surjective s
  rw [show ((channel a b).run ρ).matrix (Fintype.equivFin a.Basis x,i) (Fintype.equivFin a.Basis y,j) =
    (channel a b).toKraus.apply ρ.matrix (Fintype.equivFin a.Basis x,i) (Fintype.equivFin a.Basis y,j) from rfl,
    apply_entry, QKD.Guessing.CQ.density_block]
  rfl

end
end Foundation.Quantum.SecondRegister
