import Foundation.Crypto.Semantics.Probability.KernelRecovery
import Mathlib.Data.Fintype.EquivFin

/-! Exact recovery on equally large finite state spaces forces a permutation.
Thus a marginal-preserving recoverable kernel cannot change the multiset of
atom masses unless it has more intermediate states or a weaker requirement. -/
namespace Foundation.Probability.KernelRecovery
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B]

theorem equal_card_separated_pure (forward : A → PMF B)
    (card : Fintype.card A = Fintype.card B)
    (separated : Separated forward (fun _ => True)) :
    ∃ e : A ≃ B, ∀ a, forward a = PMF.pure (e a) := by
  classical
  let f : A → B := fun a => Classical.choose (forward a).support_nonempty
  have hf (a : A) : f a ∈ (forward a).support := Classical.choose_spec (forward a).support_nonempty
  have injective : Function.Injective f := by
    intro a b same
    by_contra different
    exact Set.disjoint_left.mp (separated a trivial b trivial different) (hf a) (same ▸ hf b)
  have bijective : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨injective,card⟩
  let e : A ≃ B := Equiv.ofBijective f bijective
  refine ⟨e,?_⟩
  intro a
  have support_eq : (forward a).support = {f a} := by
    ext b
    constructor
    · intro supported
      obtain ⟨x,rfl⟩ := bijective.2 b
      have same : x = a := by
        by_contra different
        exact Set.disjoint_left.mp (separated x trivial a trivial different) (hf x) supported
      subst x
      rfl
    · intro same
      exact Set.mem_singleton_iff.mp same ▸ hf a
  have mass : forward a (f a) = 1 := (PMF.apply_eq_one_iff _ _).mpr support_eq
  ext b
  by_cases same : b = f a
  · subst b
    simpa only [e, Equiv.ofBijective_apply, PMF.pure_apply_self] using mass
  · have zero : forward a b = 0 := by
      by_contra nonzero
      have supported := (PMF.mem_support_iff _ _).mpr nonzero
      rw [support_eq] at supported
      exact same (Set.mem_singleton_iff.mp supported)
    simpa only [e, Equiv.ofBijective_apply, PMF.pure_apply, if_neg same] using zero

theorem equal_card_recovery_pure (forward : A → PMF B) (reverse : B → PMF A)
    (card : Fintype.card A = Fintype.card B)
    (recovers : ∀ a, (forward a).bind reverse = PMF.pure a) :
    ∃ e : A ≃ B, ∀ a, forward a = PMF.pure (e a) :=
  equal_card_separated_pure forward card
    (recovery_implies_separated forward reverse (fun _ => True) (fun a _ => recovers a))

theorem equal_card_preserving_recovery (p : PMF A) (q : PMF B)
    (forward : A → PMF B) (reverse : B → PMF A)
    (card : Fintype.card A = Fintype.card B) (preserve : p.bind forward = q)
    (recovers : ∀ a, (forward a).bind reverse = PMF.pure a) :
    ∃ e : A ≃ B, (∀ a, forward a = PMF.pure (e a)) ∧ q = p.map e := by
  obtain ⟨e,he⟩ := equal_card_recovery_pure forward reverse card recovers
  refine ⟨e,he,?_⟩
  rw [← preserve]
  rw [show forward = (fun a => PMF.pure (e a)) from funext he]
  rfl

theorem equal_card_preserving_atom (p : PMF A) (q : PMF B)
    (forward : A → PMF B) (reverse : B → PMF A)
    (card : Fintype.card A = Fintype.card B) (preserve : p.bind forward = q)
    (recovers : ∀ a, (forward a).bind reverse = PMF.pure a) :
    ∃ e : A ≃ B, ∀ a, q (e a) = p a := by
  classical
  obtain ⟨e,_,he⟩ := equal_card_preserving_recovery p q forward reverse card preserve recovers
  refine ⟨e,?_⟩
  intro a
  rw [he, PMF.map_apply]
  simp [e.injective.eq_iff]

end
end Foundation.Probability.KernelRecovery
