import Foundation.Crypto.Semantics.Procedure

/-! Lift a proved component into a continuing caller. Only steps before the
component boundary must simulate; returning to the caller remains charged.
Readers below are semantic observations of full physical configurations. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {Source : Type u} {Input : Type v} {Output : Type w} {Target : Type x}
  {sourceStep : Source → PMF Source}

/-- Stop at the first component boundary, removing only absorbing padding. -/
theorem stopped_frames (P : Procedure sourceStep Input Output) (input : Input)
    (boundary : Source → Bool)
    (hExit : ∀ output ∈ (P.semantics input).support, boundary (P.exit input output) = true)
    (hAbsorb : ∀ state, boundary state = true → sourceStep state = PMF.pure state) :
    (runToBoundary sourceStep boundary (P.budget input) (P.entry input)).map Prod.fst =
      (P.semantics input).map (P.exit input) := by
  have hRun := P.final_run input (fun output hOutput => hAbsorb _ (hExit output hOutput))
    (P.budget input) (Nat.le_refl _)
  have hComplete : ∀ final ∈ (eval sourceStep (P.budget input) (P.entry input)).support,
      boundary final = true := by
    intro final hFinal
    rw [hRun, PMF.mem_support_map_iff] at hFinal
    obtain ⟨output, hOutput, he⟩ := hFinal
    subst final
    exact hExit output hOutput
  have h := (Block.stopped sourceStep boundary (P.budget input) (P.entry input)).final_law
    (fun result hResult => hAbsorb result.1
      (runToBoundary_completes sourceStep boundary _ _ hComplete result hResult))
    (P.budget input) (Nat.le_refl _)
  exact h.symm.trans hRun

theorem stopped_reader (P : Procedure sourceStep Input Output) (input : Input)
    (boundary : Source → Bool)
    (hExit : ∀ output ∈ (P.semantics input).support, boundary (P.exit input output) = true)
    (hAbsorb : ∀ state, boundary state = true → sourceStep state = PMF.pure state)
    (read : Source → Output) (hRead : ∀ output, read (P.exit input output) = output)
    (result : Source × Nat)
    (hResult : result ∈ (runToBoundary sourceStep boundary (P.budget input) (P.entry input)).support) :
    P.exit input (read result.1) = result.1 := by
  have hFrame : result.1 ∈ ((runToBoundary sourceStep boundary (P.budget input) (P.entry input)).map Prod.fst).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hResult, rfl⟩
  rw [P.stopped_frames input boundary hExit hAbsorb, PMF.mem_support_map_iff] at hFrame
  obtain ⟨output, _, he⟩ := hFrame
  rw [← he, hRead]

/-- The surrounding step relation is unchanged. Its post-boundary transfers
are executed by the residual law, rather than hidden inside an embedding. -/
noncomputable def liftBoundary (P : Procedure sourceStep Input Output)
    (sourceBoundary : Source → Bool)
    (hExit : ∀ input output, output ∈ (P.semantics input).support →
      sourceBoundary (P.exit input output) = true)
    (hAbsorb : ∀ state, sourceBoundary state = true → sourceStep state = PMF.pure state)
    (read : Input → Source → Output) (hRead : ∀ input output, read input (P.exit input output) = output)
    (targetStep : Target → PMF Target) (targetBoundary : Target → Bool) (embed : Source → Target)
    (hBoundary : ∀ state, targetBoundary (embed state) = sourceBoundary state)
    (hStep : ∀ state, sourceBoundary state = false →
      targetStep (embed state) = (sourceStep state).map embed) : Procedure targetStep Input Output where
  entry := fun input => embed (P.entry input)
  exit := fun input output => embed (P.exit input output)
  semantics := P.semantics
  costed := fun input =>
    (runToBoundary sourceStep sourceBoundary (P.budget input) (P.entry input)).map
      (fun result => (read input result.1, result.2))
  budget := P.budget
  bounded := by
    intro input result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨source, hSource, he⟩ := hResult
    subst result
    exact runToBoundary_bounded sourceStep sourceBoundary _ _ source hSource
  correct := by
    intro input
    have h := congrArg (fun p => p.map (read input))
      (P.stopped_frames input sourceBoundary (hExit input) hAbsorb)
    simp only [PMF.map_comp, Function.comp_def, hRead] at h
    change _ = (P.semantics input).map id at h
    rw [PMF.map_id] at h
    simpa only [PMF.map_comp, Function.comp_def] using h
  law := by
    intro input horizon hBudget
    have h := runToBoundary_law targetStep targetBoundary (P.budget input) horizon
      (embed (P.entry input)) hBudget
    rw [runToBoundary_map sourceStep targetStep sourceBoundary targetBoundary embed hBoundary hStep] at h
    simp only [PMF.bind_map, Function.comp_def] at h ⊢
    rw [h]
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext result hResult
    rw [P.stopped_reader input sourceBoundary (hExit input) hAbsorb (read input) (hRead input) result hResult]

end Foundation.Probability.TimedExecution.Procedure
