import Foundation.Crypto.Semantics.Procedure

/-! Give different component contracts one common physical output type.
The complete exit state and its joint cost distribution are preserved;
private data is not erased merely to simplify the contract's result type. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Input : Type v} {Output : Type w} {step : State → PMF State}

noncomputable def physical (P : Procedure step Input Output) : Procedure step Input State where
  entry := P.entry
  exit := fun _ state => state
  semantics := fun input => (P.semantics input).map (P.exit input)
  costed := fun input => (P.costed input).map (fun result => (P.exit input result.1, result.2))
  budget := P.budget
  bounded := by
    intro input result h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨source, hs, he⟩ := h
    subst result
    exact P.bounded input source hs
  correct := by
    intro input
    have h := congrArg (fun distribution => distribution.map (P.exit input)) (P.correct input)
    simpa only [PMF.map_comp, Function.comp_def] using h
  law := by
    intro input horizon hBudget
    simp only [PMF.bind_map, Function.comp_def]
    exact P.law input horizon hBudget

theorem physical_budget (P : Procedure step Input Output) (input : Input) :
    P.physical.budget input = P.budget input := rfl

theorem physical_costed (P : Procedure step Input Output) (input : Input) :
    P.physical.costed input = (P.costed input).map (fun result => (P.exit input result.1, result.2)) := rfl

/-- The new result is exactly the physical exit marginal of the original
joint cost law, not an observation that drops retained private state. -/
theorem physical_semantics (P : Procedure step Input Output) (input : Input) :
    P.physical.semantics input = (P.costed input).map (fun result => P.exit input result.1) := by
  change (P.semantics input).map (P.exit input) = _
  rw [← P.correct input, PMF.map_comp]
  rfl

end Foundation.Probability.TimedExecution.Procedure
