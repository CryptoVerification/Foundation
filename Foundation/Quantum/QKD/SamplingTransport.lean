import Foundation.Quantum.QKD.Sampling

/-! Exact transport of finite uniform nonreplacement samples along an
embedding. Renaming positions neither changes their probabilities nor
assumes independent error patterns. -/
namespace Foundation.Quantum.QKD.Sampling
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem sample_congr {α : Type*} [DecidableEq α] {U V : Finset α} (h : U = V)
    (k : Nat) (hU : k ≤ U.card) (hV : k ≤ V.card) : sample U k hU = sample V k hV := by
  subst V
  rfl

theorem uniform_map_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) (hs : s.Nonempty) :
    (PMF.uniformOfFinset s hs).map f = PMF.uniformOfFinset (s.map f) (hs.map) := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hb
    rw [PMF.map_apply, tsum_eq_single a]
    · simp [PMF.uniformOfFinset_apply]
    · intro j hj
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hj (f.injective h).symm)
  · have hf (a : α) : b ≠ f a := fun h => hb ⟨a,h.symm⟩
    rw [PMF.map_apply]
    simp only [hf, ite_false, tsum_zero]
    symm
    apply PMF.uniformOfFinset_apply_of_notMem
    intro h
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp h
    exact hf a ha.symm

theorem sample_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (U : Finset α) (k : Nat) (hk : k ≤ U.card) :
    (sample U k hk).map (Finset.map f) =
      sample (U.map f) k (by simpa only [Finset.card_map] using hk) := by
  unfold sample
  have h := uniform_map_embedding
    (Finset.mapEmbedding f).toEmbedding (U.powersetCard k) (Finset.powersetCard_nonempty.mpr hk)
  have hc : ((Finset.mapEmbedding f).toEmbedding : Finset α → Finset β) = Finset.map f := by
    funext S
    rfl
  rw [hc] at h
  simpa only [Finset.powersetCard_map] using h

end
end Foundation.Quantum.QKD.Sampling
