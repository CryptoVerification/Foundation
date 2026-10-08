import Foundation.Crypto.Semantics.ResourceEnvelope
import Foundation.Crypto.Semantics.Framing

/-! Reuse any monotone resource envelope while retaining arbitrary saved
caller data. Physical saved data is charged, and framing is an entry
precondition rather than an uncharged construction or copy operation. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth.Envelope
universe u v
variable {State : Type u} {Saved : Type v} {step : State → PMF State}
    (E : ResourceGrowth.Envelope step) (savedSize : Saved → Nat)

/-- Saved tapes, keys, histories or external state are included in both the
analysis extent and the actual retained-data measure. -/
noncomputable def framed : ResourceGrowth.Envelope (framedStep (Saved := Saved) step) where
  extent := fun frame => E.extent frame.1 + savedSize frame.2
  retained := fun frame => E.retained frame.1 + savedSize frame.2
  bound := fun extent => E.bound extent + extent
  monotone := by
    intro a b h
    exact Nat.add_le_add (E.monotone h) h
  covers := by
    intro frame
    have hb := E.covers frame.1
    have hm := E.monotone (Nat.le_add_right (E.extent frame.1) (savedSize frame.2))
    change E.retained frame.1 + savedSize frame.2 ≤
      E.bound (E.extent frame.1 + savedSize frame.2) + (E.extent frame.1 + savedSize frame.2)
    omega
  increment := E.increment
  grows := by
    intro start target h
    rw [framedStep, PMF.mem_support_map_iff] at h
    obtain ⟨source, hs, he⟩ := h
    subst target
    have hb := E.grows start.1 source hs
    change E.extent source + savedSize start.2 ≤ E.extent start.1 + savedSize start.2 + E.increment
    omega

/-- Framing preserves the real saved value on every supported execution
prefix, while allowing arbitrary nonlinear resource bounds for the worker. -/
theorem framed_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : State × Saved)
    (h : target ∈ (eval (framedStep step) elapsed start).support) :
    E.retained target.1 + savedSize target.2 ≤
      E.bound (E.extent start.1 + savedSize start.2 + horizon * E.increment) +
        (E.extent start.1 + savedSize start.2 + horizon * E.increment) :=
  (E.framed savedSize).peak horizon elapsed hElapsed start target h

end Foundation.Probability.TimedExecution.ResourceGrowth.Envelope
