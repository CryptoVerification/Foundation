import Foundation.Quantum.BasisTransport
import Foundation.Quantum.QKD.SeededSubnormalized
import Foundation.Quantum.QKD.CommonKeyComposition
import Foundation.Quantum.QKD.HashDistance

/-! Exact reordering of the public-seed hash experiment into one key/public
register, with the entire quantum side system retained. -/
namespace Foundation.Quantum.QKD.HashLayout
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {X K L S : Type} [Fintype X] [Fintype K] [Fintype L] [Fintype S]
  [DecidableEq K] [DecidableEq L] [DecidableEq S] {e : Space}

abbrev Nested (K L S : Type) [Fintype K] [Fintype L] [Fintype S] (e : Space) :=
  Guessing.publicSpace S (Guessing.publicSpace K (Guessing.publicSpace L e))
abbrev Flat (K L S : Type) [Fintype K] [Fintype L] [Fintype S] (e : Space) :=
  Guessing.publicSpace (K × (L × S)) e

/-- This is a bijection of basis labels, preserving the quantum coordinate. -/
def basis : (Flat K L S e).Basis ≃ (Nested K L S e).Basis where
  toFun i := let p := (Fintype.equivFin (K × (L × S))).symm i.1
    (Fintype.equivFin S p.2.2, Fintype.equivFin K p.1, Fintype.equivFin L p.2.1, i.2)
  invFun i := (Fintype.equivFin (K × (L × S))
    ((Fintype.equivFin K).symm i.2.1,
      ((Fintype.equivFin L).symm i.2.2.1,(Fintype.equivFin S).symm i.1)),i.2.2.2)
  left_inv i := by simp
  right_inv i := by simp

def output (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K) : State (K × (L × S)) e :=
  relabel (seed p ρ) (fun sx => (hash sx.1 sx.2.1,(sx.2.2,sx.1)))

theorem output_block (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K)
    (k : K) (l : L) (s : S) :
    (output ρ p hash).block (k,(l,s)) = ((p s).toReal:ℂ) • ∑ x, if hash s x = k then ρ.block (x,l) else 0 := by
  simp [output, relabel, seed, Fintype.sum_prod_type, Prod.mk.injEq, ite_and, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hi (s₀ : S) :
      (if hash s₀ x = k then (if s₀ = s then (p s₀).toReal • ρ.block (x,l) else 0) else 0) =
        if s₀ = s then (if hash s₀ x = k then (p s₀).toReal • ρ.block (x,l) else 0) else 0 := by
    by_cases hs : s₀ = s <;> simp [hs]
  simp_rw [hi]
  simp

theorem output_public (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K) (l : L) (s : S) :
    (∑ k, (output ρ p hash).block (k,(l,s))) = ((p s).toReal:ℂ) • ∑ x, ρ.block (x,l) := by
  simp_rw [output_block]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp

theorem public_block (ρ : State (X × L) e) (x : X) (l m : L) (i j : e.Basis) :
    (withPublic ρ).block x (Fintype.equivFin L l,i) (Fintype.equivFin L m,j) =
      if l = m then ρ.block (x,l) i j else 0 := by
  have h : (withPublic ρ).block x = ClassicalBlocks.of (fun l => ρ.block (x,l)) := by
    rw [ClassicalBlocks.representation]
    rfl
  rw [h, ClassicalBlocks.encoded]

/-- The real hash output is the same operator with basis coordinates reordered. -/
theorem real (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K) :
    BasisTransport.operator (basis (K := K) (L := L) (S := S) (e := e))
      (publicMixture p (fun s => Collision.hashed (withPublic ρ).block (hash s))) =
        joint (output ρ p hash) := by
  apply Matrix.ext
  intro ⟨r,i⟩ ⟨t,j⟩
  obtain ⟨⟨k,l,s⟩,rfl⟩ := (Fintype.equivFin (K × (L × S))).surjective r
  obtain ⟨⟨k',l',s'⟩,rfl⟩ := (Fintype.equivFin (K × (L × S))).surjective t
  change publicMixture p _ (basis (K := K) (L := L) (S := S) (e := e) (Fintype.equivFin _ (k,(l,s)),i))
    (basis (K := K) (L := L) (S := S) (e := e) (Fintype.equivFin _ (k',(l',s')),j)) = _
  simp only [basis, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rw [publicMixture_block, joint_block (output ρ p hash)]
  unfold Collision.hashed
  rw [ClassicalBlocks.encoded]
  simp only [Collision.grouped, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  have hb (x : X) := public_block ρ x l l' i j
  simp_rw [hb]
  by_cases hs : s = s' <;> by_cases hk : k = k' <;> by_cases hl : l = l' <;>
    simp [hs, hk, hl, Prod.mk.injEq, output_block, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.ite_apply, smul_eq_mul]

variable [Nonempty K]

/-- The comparator becomes the same uniform key with exactly the same
public/quantum marginal as the real flat output. -/
theorem ideal (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K) :
    BasisTransport.operator (basis (K := K) (L := L) (S := S) (e := e))
      (publicMixture p (fun _ => Collision.uniformComparator (Y := K) (withPublic ρ).block)) =
        joint (CommonKey.uniformize (output ρ p hash)) := by
  apply Matrix.ext
  intro ⟨r,i⟩ ⟨t,j⟩
  obtain ⟨⟨k,l,s⟩,rfl⟩ := (Fintype.equivFin (K × (L × S))).surjective r
  obtain ⟨⟨k',l',s'⟩,rfl⟩ := (Fintype.equivFin (K × (L × S))).surjective t
  change publicMixture p _ (basis (K := K) (L := L) (S := S) (e := e) (Fintype.equivFin _ (k,(l,s)),i))
    (basis (K := K) (L := L) (S := S) (e := e) (Fintype.equivFin _ (k',(l',s')),j)) = _
  simp only [basis, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rw [publicMixture_block, joint_block (CommonKey.uniformize (output ρ p hash))]
  unfold Collision.uniformComparator
  rw [ClassicalBlocks.encoded]
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  have hb (x : X) := public_block ρ x l l' i j
  simp_rw [hb]
  have hu (a : K) (m : L) (t : S) : (CommonKey.uniformize (output ρ p hash)).block (a,(m,t)) =
      ((1/(Fintype.card K:ℝ):ℝ):ℂ) • (((p t).toReal:ℂ) • ∑ x, ρ.block (x,m)) := by
    change ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ b, (output ρ p hash).block (b,(m,t)) = _
    rw [output_public]
  by_cases hs : s = s' <;> by_cases hk : k = k' <;> by_cases hl : l = l' <;>
    simp [hs, hk, hl, Prod.mk.injEq, hu, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul, mul_comm, mul_assoc]

/-- Every joint observation bound transfers across the proved layout equalities. -/
theorem secrecy (ρ : State (X × L) e) (p : PMF S) (hash : S → X → K) (ε : ℝ)
    (h : OperatorApprox
      (publicMixture p (fun s => Collision.hashed (withPublic ρ).block (hash s)))
      (publicMixture p (fun _ => Collision.uniformComparator (Y := K) (withPublic ρ).block)) ε) :
    OperatorApprox (joint (output ρ p hash)) (joint (CommonKey.uniformize (output ρ p hash))) ε := by
  have hh := BasisTransport.approx (basis (K := K) (L := L) (S := S) (e := e)) _ _ ε h
  rw [real, ideal] at hh
  exact hh

end
end Foundation.Quantum.QKD.HashLayout
