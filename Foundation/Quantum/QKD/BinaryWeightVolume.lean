import Foundation.Quantum.QKD.PairwiseWeightDeviation
import Mathlib.Data.Finset.Powerset

/-! Exact binary Hamming-ball volume by a weight-preserving equivalence with
finite subsets. Counts are sums of binomial coefficients, not enumeration of
all binary words. -/
namespace Foundation.Quantum.QKD.BinaryWeightVolume
noncomputable section
set_option backward.isDefEq.respectTransparency false

def support {n : Nat} (x : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = 1)

def characteristic {n : Nat} (S : Finset (Fin n)) : Fin n → Fin 2 :=
  fun i => if i ∈ S then 1 else 0

def bitsEquiv (n : Nat) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun := support
  invFun := characteristic
  left_inv x := by
    funext i
    have hx : x i = 0 ∨ x i = 1 := by
      have h := (x i).isLt
      rcases (show (x i).val = 0 ∨ (x i).val = 1 by omega) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases hx with hx | hx <;> simp [support, characteristic, hx]
  right_inv S := by
    ext i
    simp [support, characteristic]

def ball (n radius : Nat) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter (fun x => (support x).card ≤ radius)

def volume (n radius : Nat) : Nat := ∑ j ∈ Finset.range (radius+1), Nat.choose n j

theorem sphere_card (n j : Nat) :
    (Finset.univ.filter (fun x : Fin n → Fin 2 => (support x).card = j)).card = Nat.choose n j := by
  have he : (Finset.univ.filter (fun x : Fin n → Fin 2 => (support x).card = j)).map (bitsEquiv n).toEmbedding =
      (Finset.univ : Finset (Fin n)).powersetCard j := by
    ext S
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hS
      refine ⟨(bitsEquiv n).symm S,?_,(bitsEquiv n).apply_symm_apply S⟩
      change ((bitsEquiv n) ((bitsEquiv n).symm S)).card = j
      simpa only [Equiv.apply_symm_apply] using hS
  have h := congrArg Finset.card he
  simpa only [Finset.card_map, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using h

theorem ball_card (n radius : Nat) : (ball n radius).card = volume n radius := by
  classical
  have he : ball n radius = (Finset.range (radius+1)).biUnion
      (fun j => Finset.univ.filter (fun x : Fin n → Fin 2 => (support x).card = j)) := by
    ext x
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨(support x).card,by omega,rfl⟩
    · rintro ⟨j,hj,hx⟩
      omega
  rw [he, Finset.card_biUnion]
  · simp only [sphere_card, volume]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    exact hij (hxi.symm.trans hxj)

end
end Foundation.Quantum.QKD.BinaryWeightVolume
