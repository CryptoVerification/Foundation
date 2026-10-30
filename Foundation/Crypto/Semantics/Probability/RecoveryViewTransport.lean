import Foundation.Crypto.Semantics.Probability.KernelRecovery

/-! Marginal-preserving recovery on ambient states induces recovery on finite
faithful views. Positive input masses force every used intermediate state
into the specified target view; no hidden zero-marginal side state is allowed. -/
namespace Foundation.Probability.RecoveryViewTransport
noncomputable section
variable {A B S T : Type}

def forward (encode : A → S) (read : T → B) (kernel : S → PMF T) (a : A) : PMF B :=
  (kernel (encode a)).map read

def reverse (encode : B → T) (read : S → A) (kernel : T → PMF S) (b : B) : PMF A :=
  (kernel (encode b)).map read

theorem used_target_in_view (p : PMF A) (q : PMF B) (source : A → S) (target : B → T)
    (read : T → B) (read_target : Function.LeftInverse read target)
    (kernel : S → PMF T) (full : ∀ a, a ∈ p.support)
    (preserve : (p.map source).bind kernel = q.map target)
    (a : A) (t : T) (supported : t ∈ (kernel (source a)).support) : target (read t) = t := by
  have source_supported : source a ∈ (p.map source).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨a,full a,rfl⟩
  have member : t ∈ ((p.map source).bind kernel).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨source a,source_supported,supported⟩
  rw [preserve, PMF.mem_support_map_iff] at member
  obtain ⟨b,_,same⟩ := member
  rw [← same, read_target b]

theorem induced_preserves (p : PMF A) (q : PMF B) (source : A → S) (target : B → T)
    (read : T → B) (read_target : Function.LeftInverse read target) (kernel : S → PMF T)
    (preserve : (p.map source).bind kernel = q.map target) :
    p.bind (forward source read kernel) = q := by
  calc
    _ = ((p.map source).bind kernel).map read := by
      rw [PMF.map_bind, PMF.bind_map]
      rfl
    _ = (q.map target).map read := congrArg (fun law => law.map read) preserve
    _ = q := by
      rw [PMF.map_comp, show read ∘ target = id from funext read_target, PMF.map_id]

theorem induced_recovers (p : PMF A) (q : PMF B) (source : A → S) (target : B → T)
    (read_source : S → A) (read_target : T → B)
    (source_inverse : Function.LeftInverse read_source source)
    (target_inverse : Function.LeftInverse read_target target)
    (kernel : S → PMF T) (back : T → PMF S) (full : ∀ a, a ∈ p.support)
    (preserve : (p.map source).bind kernel = q.map target)
    (recovers : ∀ a, (kernel (source a)).bind back = PMF.pure (source a)) (a : A) :
    (forward source read_target kernel a).bind (reverse target read_source back) = PMF.pure a := by
  calc
    _ = (kernel (source a)).bind (fun t => (back t).map read_source) := by
      rw [forward, PMF.bind_map]
      apply bind_congr_of_support
      intro t supported
      change (back (target (read_target t))).map read_source = _
      rw [used_target_in_view p q source target read_target target_inverse kernel full preserve a t supported]
    _ = ((kernel (source a)).bind back).map read_source := (PMF.map_bind _ _ _).symm
    _ = PMF.pure a := by rw [recovers, PMF.pure_map, source_inverse]

end
end Foundation.Probability.RecoveryViewTransport
