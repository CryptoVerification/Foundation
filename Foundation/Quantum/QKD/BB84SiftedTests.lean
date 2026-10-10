import Foundation.Quantum.QKD.BB84SiftedBases
import Foundation.Quantum.QKD.SamplingTransport

/-! Reindex actual BB84 test sets from original to selected positions.
No assumption about independent error bits is made. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def indexEmbedding {n : Nat} (M : Finset (Fin n)) : Fin (selectedCount M) ↪ Fin n where
  toFun i := (selectedIndex M i).val
  inj' := by
    intro i j h
    exact (selectedIndex M).injective (Subtype.ext h)

def liftTest {n : Nat} (M : Finset (Fin n)) (S : Finset (Fin (selectedCount M))) : Finset (Fin n) :=
  S.map (indexEmbedding M)

def restrictTest {n : Nat} (M T : Finset (Fin n)) : Finset (Fin (selectedCount M)) :=
  Finset.univ.filter (fun i => indexEmbedding M i ∈ T)

theorem mem_restrictTest {n : Nat} (M T : Finset (Fin n)) (i : Fin (selectedCount M)) :
    i ∈ restrictTest M T ↔ indexEmbedding M i ∈ T := by simp [restrictTest]

theorem restrict_lift {n : Nat} (M : Finset (Fin n)) (S : Finset (Fin (selectedCount M))) :
    restrictTest M (liftTest M S) = S := by
  ext i
  simp [restrictTest, liftTest]

theorem lift_subset {n : Nat} (M : Finset (Fin n)) (S : Finset (Fin (selectedCount M))) :
    liftTest M S ⊆ M := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
  exact (selectedIndex M j).property

theorem lift_restrict {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M) :
    liftTest M (restrictTest M T) = T := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (mem_restrictTest M T j).mp hj
  · intro hi
    let j := (selectedIndex M).symm ⟨i,hT hi⟩
    have hj : indexEmbedding M j = i := by simp [indexEmbedding, j]
    exact Finset.mem_map.mpr ⟨j, (mem_restrictTest M T j).mpr (hj.symm ▸ hi), hj⟩

theorem lift_card {n : Nat} (M : Finset (Fin n)) (S : Finset (Fin (selectedCount M))) :
    (liftTest M S).card = S.card := Finset.card_map _

theorem restrict_card {n : Nat} (M T : Finset (Fin n)) (hT : T ⊆ M) :
    (restrictTest M T).card = T.card := by
  rw [← lift_card M, lift_restrict M T hT]

theorem lift_univ {n : Nat} (M : Finset (Fin n)) :
    liftTest M Finset.univ = M := by
  have h : restrictTest M M = Finset.univ := by
    ext i
    simp [restrictTest, indexEmbedding]
  rw [← h, lift_restrict M M (Finset.Subset.refl M)]

theorem selectedCount_eq_card {n : Nat} (M : Finset (Fin n)) : selectedCount M = M.card :=
  Fintype.card_coe M

theorem lift_powersetCard {n : Nat} (M : Finset (Fin n)) (k : Nat) :
    ((Finset.univ : Finset (Fin (selectedCount M))).powersetCard k).map
      ⟨liftTest M, by intro S T h; simpa only [restrict_lift] using congrArg (restrictTest M) h⟩ =
      M.powersetCard k := by
  ext T
  simp only [Finset.mem_map, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact ⟨lift_subset M S, (lift_card M S).trans hS⟩
  · rintro ⟨hT,hcard⟩
    exact ⟨restrictTest M T, (restrict_card M T hT).trans hcard, lift_restrict M T hT⟩

theorem sample_lift {n : Nat} (M : Finset (Fin n)) (k : Nat) (hk : k ≤ M.card) :
    (Sampling.sample (Finset.univ : Finset (Fin (selectedCount M))) k
      (by simpa only [Finset.card_univ, Fintype.card_fin, selectedCount_eq_card] using hk)).map
      (liftTest M) = Sampling.sample M k hk := by
  let U : Finset (Fin (selectedCount M)) := Finset.univ
  have hU : k ≤ U.card := by
    simpa only [U, Finset.card_univ, Fintype.card_fin, selectedCount_eq_card] using hk
  have h := Sampling.sample_map (indexEmbedding M) U k hU
  have hu : Finset.map (indexEmbedding M) Finset.univ = M := lift_univ M
  have hc : Finset.map (indexEmbedding M) = liftTest M := by funext S; rfl
  exact (congrArg (fun f => (Sampling.sample U k hU).map f) hc.symm).trans
    (h.trans (Sampling.sample_congr hu k _ hk))

theorem testDistribution_lift {n : Nat} (M : Finset (Fin n)) (k : Nat) :
    (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k).map
      (liftTest M) = BB84SiftingRandomness.testDistribution M k := by
  unfold BB84SiftingRandomness.testDistribution
  simp only [Finset.card_univ, Fintype.card_fin, selectedCount_eq_card]
  split_ifs with hk
  · exact sample_lift M k hk
  · rw [PMF.pure_map]
    rfl

end
end Foundation.Quantum.QKD.BB84SiftedInput
