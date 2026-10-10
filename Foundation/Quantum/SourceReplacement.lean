import Foundation.Quantum.PureProjection
import Foundation.Quantum.QKD.Qubits

/-! Finite source replacement as an equality of full conditional operators.
A normalized entangled pair and a local real symmetric basis measurement give
the same weighted remote state as uniform prepare-and-send, after an arbitrary
finite Kraus operation. This module does not assume protocol security. -/
namespace Foundation.Quantum.SourceReplacement
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

theorem rank_conjugate (M : Op a b) (v : a.Basis → ℂ) :
    M * rank v v * M.conjTranspose = rank (M.mulVec v) (M.mulVec v) := by
  simp only [rank, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  funext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply, star_sum, star_mul, mul_comm]

def pairVector (a : Space) (c : ℂ) : (Space.tensor a a).Basis → ℂ :=
  fun p => if p.1 = p.2 then c else 0

theorem pair_unit (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1) :
    bracket (e := .tensor a a) (pairVector a c) (pairVector a c) = 1 := by
  simp only [bracket, pairVector, Fintype.sum_prod_type]
  have h (i : a.Basis) : (∑ j : a.Basis,
      star (if i = j then c else 0) * (if i = j then c else 0)) = c*star c := by
    simp [mul_comm]
  simp_rw [h]
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using hc

def pair (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1) : Density (.tensor a a) :=
  pure (pairVector a c) (pair_unit a c hc)

/-- Alice acts on the second tensor factor; the first factor is transmitted. -/
def rotate (a b : Space) (U : Operator a) (hU : U.conjTranspose*U = 1) :
    Channel (.tensor b a) (.tensor b a) :=
  Channel.ofIsometry (Op.tensor (Op.ident b) U)
    (QKD.tensor_isometry _ _ (by simp [Op.ident]) hU)

theorem rotate_vector (a : Space) (c : ℂ) (U : Operator a) :
    (Op.tensor (Op.ident a) U).mulVec (pairVector a c) = fun p => c*U p.2 p.1 := by
  funext p
  rcases p with ⟨i,x⟩
  simp [Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap, Matrix.mulVec,
    dotProduct, pairVector, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_comm]

theorem rotated_pair (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1)
    (U : Operator a) (hU : U.conjTranspose*U = 1) :
    ((rotate a a U hU).run (pair a c hc)).matrix = rank (e := .tensor a a) (fun p => c*U p.2 p.1) (fun p => c*U p.2 p.1) := by
  change (Kraus.single (Op.tensor (Op.ident a) U)).apply (rank (pairVector a c) (pairVector a c)) = _
  rw [Kraus.single_apply, rank_conjugate, rotate_vector]

def slice (ρ : Operator (.tensor b a)) (x : a.Basis) : Operator b :=
  ρ.submatrix (fun i => (i,x)) (fun i => (i,x))

/-- A local operation commutes with retaining a diagonal outcome block of the
other subsystem. Every remote coherence coordinate is kept in this equality. -/
theorem amplify_slice (K : Kraus a b) (r : Space) (ρ : Operator (.tensor a r)) (x : r.Basis) :
    slice ((K.amplify r).apply ρ) x = K.apply (slice ρ x) := by
  ext i j
  rw [show slice ((K.amplify r).apply ρ) x i j = (K.amplify r).apply ρ (i,x) (j,x) from rfl,
    Kraus.amplify_apply_entry]
  simp only [Kraus.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    slice, Matrix.submatrix_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm

theorem prepared_matrix (a : Space) (U : Operator a) (hU : U.conjTranspose*U = 1) (x : a.Basis) :
    ((Channel.ofIsometry U hU).run (basisDensity a x)).matrix = rank (fun i => U i x) (fun i => U i x) := by
  ext i j
  simp [Channel.run, Channel.ofIsometry, Kraus.single_apply, basisDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, rank, Matrix.vecMulVec_apply, Pi.star_apply,
    mul_ite, ite_mul]

theorem rotated_slice (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1)
    (U : Operator a) (hU : U.conjTranspose*U = 1) (hsym : ∀ i j, U i j = U j i) (x : a.Basis) :
    slice ((rotate a a U hU).run (pair a c hc)).matrix x =
      (c*star c) • ((Channel.ofIsometry U hU).run (basisDensity a x)).matrix := by
  rw [rotated_pair, prepared_matrix]
  ext i j
  simp only [slice, Matrix.submatrix_apply, rank, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, smul_eq_mul, star_mul, hsym x i, hsym x j]
  ring

/-- Source replacement after a genuinely arbitrary joint Kraus attack. The
scalar is the actual Alice outcome weight, not a renormalized conditional state. -/
theorem replacement (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1)
    (U : Operator a) (hU : U.conjTranspose*U = 1) (hsym : ∀ i j, U i j = U j i)
    (C : Channel a b) (x : a.Basis) :
    slice ((C.amplify a).run ((rotate a a U hU).run (pair a c hc))).matrix x =
      (c*star c) • (C.run ((Channel.ofIsometry U hU).run (basisDensity a x))).matrix := by
  change slice ((C.toKraus.amplify a).apply _) x = _
  rw [amplify_slice, rotated_slice a c hc U hU hsym]
  exact C.toKraus.linear.map_smul _ _

end
end Foundation.Quantum.SourceReplacement
