import Foundation.Quantum.QKD.Guessing
import Foundation.Quantum.QKD.BB84Randomized

/-! Classical-quantum blocks are actual joint density operators. Conversely,
reading each classical diagonal block of any joint density gives a normalized
CQ state; off-diagonal classical coherence is not asserted to survive this
reading. The randomized BB84 output is connected by this construction. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {e : Space}

def CQ.density (ρ : CQ X e) : Density (.tensor (.register (Fintype.card X)) e) where
  matrix := ∑ x, Matrix.kronecker (basisDensity (.register (Fintype.card X)) (Fintype.equivFin X x)).matrix (ρ.block x)
  positive := Matrix.posSemidef_sum _ (fun x _ =>
    (basisDensity (.register (Fintype.card X)) (Fintype.equivFin X x)).positive.kronecker (ρ.positive x))
  normalized := by
    unfold Matrix.kronecker
    simp only [Matrix.trace_sum, Matrix.trace_kronecker, (basisDensity _ _).normalized, one_mul]
    exact ρ.normalized

/-- The joint state retains exactly the specified conditional quantum block. -/
theorem CQ.density_block [DecidableEq X] (ρ : CQ X e) (x y : X) (i j : e.Basis) :
    ρ.density.matrix (Fintype.equivFin X x,i) (Fintype.equivFin X y,j) =
      if x = y then ρ.block x i j else 0 := by
  by_cases h : x = y
  · subst y
    simp [CQ.density, basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.diagonal_apply]
  · simp [CQ.density, basisDensity, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.diagonal_apply, h]

/-- Read classical blocks of a real joint state without renormalizing outcomes. -/
def ofDensity {n : Nat} (ρ : Density (.tensor (.register n) e)) : CQ (Fin n) e where
  block x := ρ.matrix.submatrix (fun i => (x,i)) (fun i => (x,i))
  positive x := ρ.positive.submatrix (fun i => (x,i))
  normalized := by
    change (∑ x : Fin n, ∑ i : e.Basis, ρ.matrix (x,i) (x,i)) = 1
    simpa only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using ρ.normalized

/-- All private raw keys and the complete public transcript remain labels;
 Eve's entire quantum system is retained from the actual block experiment. -/
def bb84Blocks {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    CQ (Fin (Fintype.card (RawProtocol.Output n))) e :=
  ofDensity (Randomized.keyState A k minKey tolerance)

end
end Foundation.Quantum.QKD.Guessing
