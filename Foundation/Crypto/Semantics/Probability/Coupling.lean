import Foundation.Crypto.Semantics.Probability.Facts

/-! Bounds from an explicit common probability space. A joint law and its
marginal equalities are proof obligations, not assumptions that two independent
experiments share randomness. These facts support indifferentiability game hops. -/
namespace Foundation.Probability

open scoped ENNReal

/-- Events which agree outside a bad event differ in probability by at most
that bad event. Agreement is required only on reachable outcomes. -/
theorem coupled_event_gap_le {α : Type*} (joint : PMF α)
    (left right bad : α → Prop)
    (agree : ∀ outcome ∈ joint.support, ¬bad outcome → (left outcome ↔ right outcome)) :
    probabilityGap (eventProb joint left) (eventProb joint right) ≤ eventProb joint bad := by
  have hl : eventProb joint left ≤ eventProb joint bad + eventProb joint right := by
    calc
      _ ≤ eventProb joint (fun outcome => bad outcome ∨ right outcome) := by
        apply eventProb_mono_of_support
        intro outcome ho hleft
        by_cases hb : bad outcome
        · exact Or.inl hb
        · exact Or.inr ((agree outcome ho hb).mp hleft)
      _ ≤ _ := eventProb_or_le joint bad right
  have hr : eventProb joint right ≤ eventProb joint bad + eventProb joint left := by
    calc
      _ ≤ eventProb joint (fun outcome => bad outcome ∨ left outcome) := by
        apply eventProb_mono_of_support
        intro outcome ho hright
        by_cases hb : bad outcome
        · exact Or.inl hb
        · exact Or.inr ((agree outcome ho hb).mpr hright)
      _ ≤ _ := eventProb_or_le joint bad left
  exact max_le (tsub_le_iff_right.mpr hl) (tsub_le_iff_right.mpr hr)

/-- Different hidden state types are allowed. The supplied common law must
have the two claimed marginal distributions; equality of observations outside
bad then gives the same error, without a factor of two. -/
theorem coupled_map_gap_le {Joint Left Right : Type*}
    (joint : PMF Joint) (leftLaw : PMF Left) (rightLaw : PMF Right)
    (projectLeft : Joint → Left) (projectRight : Joint → Right)
    (leftMarginal : joint.map projectLeft = leftLaw)
    (rightMarginal : joint.map projectRight = rightLaw)
    (leftEvent : Left → Prop) (rightEvent : Right → Prop) (bad : Joint → Prop)
    (agree : ∀ outcome ∈ joint.support, ¬bad outcome →
      (leftEvent (projectLeft outcome) ↔ rightEvent (projectRight outcome))) :
    probabilityGap (eventProb leftLaw leftEvent) (eventProb rightLaw rightEvent) ≤
      eventProb joint bad := by
  rw [← leftMarginal, ← rightMarginal, eventProb_map, eventProb_map]
  exact coupled_event_gap_le joint _ _ bad agree

end Foundation.Probability
