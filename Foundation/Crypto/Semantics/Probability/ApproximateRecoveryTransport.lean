import Foundation.Crypto.Semantics.Probability.RecoveryViewTransport
import Foundation.Crypto.Semantics.Probability.FiniteRecoveryError

/-! Projecting a full-state return to a faithful source label can only reduce
its recovery error. This transfers uniform finite-label error lower bounds
to ambient state kernels, including returns outside the source view. -/
namespace Foundation.Probability.ApproximateRecoveryTransport
noncomputable section
variable {A B S T : Type}

theorem induced_roundtrip (p : PMF A) (q : PMF B) (source : A → S) (target : B → T)
    (read_source : S → A) (read_target : T → B)
    (target_inverse : Function.LeftInverse read_target target)
    (forward : S → PMF T) (reverse : T → PMF S) (full : ∀ a, a ∈ p.support)
    (preserve : (p.map source).bind forward = q.map target) (a : A) :
    (RecoveryViewTransport.forward source read_target forward a).bind
      (RecoveryViewTransport.reverse target read_source reverse) =
      ((forward (source a)).bind reverse).map read_source := by
  rw [RecoveryViewTransport.forward, PMF.bind_map, PMF.map_bind]
  apply bind_congr_of_support
  intro t supported
  change (reverse (target (read_target t))).map read_source = _
  rw [RecoveryViewTransport.used_target_in_view p q source target read_target target_inverse forward full preserve a t supported]

open scoped BigOperators

theorem induced_failure_le [Fintype A] [Nonempty A] [Fintype B]
    (p : PMF A) (q : PMF B) (source : A → S) (target : B → T)
    (read_source : S → A) (read_target : T → B)
    (source_inverse : Function.LeftInverse read_source source)
    (target_inverse : Function.LeftInverse read_target target)
    (forward : S → PMF T) (reverse : T → PMF S) (full : ∀ a, a ∈ p.support)
    (preserve : (p.map source).bind forward = q.map target) :
    FiniteRecoveryError.failure p (RecoveryViewTransport.forward source read_target forward)
      (RecoveryViewTransport.reverse target read_source reverse) ≤
      ∑ a, (p a).toReal * (eventProb ((forward (source a)).bind reverse) (· ≠ source a)).toReal := by
  unfold FiniteRecoveryError.failure
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  rw [induced_roundtrip p q source target read_source read_target target_inverse forward reverse full preserve,
    eventProb_map]
  apply ENNReal.toReal_mono
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
  apply eventProb_mono
  intro s different same
  apply different
  rw [same,source_inverse]

end
end Foundation.Probability.ApproximateRecoveryTransport
