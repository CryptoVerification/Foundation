import Foundation.Quantum.QKD.SubnormalizedPhysical

/-! Classical diagonal registers with arbitrary quantum operator blocks.
The blocks need not be positive, so centered hash differences are supported.
All identities are equations of actual joint operators. -/
namespace Foundation.Quantum.ClassicalBlocks
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {a : Space}

/-- A block diagonal operator in the fixed encoding of the classical register. -/
def of (B : X → Operator a) : Operator (.tensor (.register (Fintype.card X)) a) :=
  fun i j => if i.1 = j.1 then B ((Fintype.equivFin X).symm i.1) i.2 j.2 else 0

theorem encoded [DecidableEq X] (B : X → Operator a) (x y : X) (i j : a.Basis) :
    of B (Fintype.equivFin X x,i) (Fintype.equivFin X y,j) = if x = y then B x i j else 0 := by
  simp [of]

theorem representation (B : X → Operator a) : of B =
    ∑ x, Matrix.kronecker (basisDensity (.register (Fintype.card X)) (Fintype.equivFin X x)).matrix (B x) := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective s
  rw [encoded]
  by_cases h : x = y
  · subst y
    simp [basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.diagonal_apply]
  · simp [basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.diagonal_apply, h]

theorem positive (B : X → Operator a) (hB : ∀ x, (B x).PosSemidef) : (of B).PosSemidef := by
  rw [representation]
  exact Matrix.posSemidef_sum _ (fun x _ => (basisDensity _ _).positive.kronecker (hB x))

theorem hermitian (B : X → Operator a) (hB : ∀ x, (B x).IsHermitian) : (of B).IsHermitian := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · subst s
    simpa only [Matrix.conjTranspose_apply, of, ite_true] using congrFun (congrFun (hB _).eq i) j
  · simp [Matrix.conjTranspose_apply, of, h, Ne.symm h]

theorem sub (B C : X → Operator a) : of (fun x => B x-C x) = of B - of C := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s <;> simp [of, Matrix.sub_apply, h]

theorem mul (B C : X → Operator a) : of (fun x => B x*C x) = of B * of C := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, of]
  by_cases h : r = s
  · subst s
    simp
  · simp [h, mul_ite, ite_mul, -Finset.sum_boole]

theorem adjoint (B : X → Operator a) : of (fun x => (B x).conjTranspose) = (of B).conjTranspose := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · subst s
    simp [of, Matrix.conjTranspose_apply]
  · simp [of, Matrix.conjTranspose_apply, h, Ne.symm h]

theorem trace (B : X → Operator a) : (of B).trace = ∑ x, (B x).trace := by
  rw [representation]
  unfold Matrix.kronecker
  simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized, one_mul]

theorem trace_square (B : X → Operator a) : (of B * of B).trace.re = ∑ x, (B x*B x).trace.re := by
  rw [← mul, trace, Complex.re_sum]

theorem constant_cost (D : Operator a) :
    (((of (fun _ : X => D))*(of (fun _ : X => D)).conjTranspose)*
      ((of (fun _ : X => D))*(of (fun _ : X => D)).conjTranspose)).trace.re =
        Fintype.card X * ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re := by
  rw [← adjoint, ← mul, trace_square]
  simp

theorem reconstruct (B C : X → Operator a) (D : Operator a)
    (h : ∀ x, B x = D.conjTranspose*C x*D) :
    of B = (of (fun _ : X => D)).conjTranspose * of C * of (fun _ : X => D) := by
  rw [← adjoint, ← mul, ← mul]
  congr 1
  funext x
  exact h x

theorem joint (ρ : QKD.Subnormalized.State X a) : of ρ.block = QKD.Subnormalized.joint ρ :=
  representation _

end
end Foundation.Quantum.ClassicalBlocks
