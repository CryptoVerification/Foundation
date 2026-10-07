import Foundation.Crypto.Semantics.TimedExecution

/-! Composable contracts for existing probabilistic transition systems.
The contract retains the complete physical exit configuration and actual
cost distribution. Returning a value is distinct from transferring control. -/
namespace Foundation.Probability.TimedExecution
universe u v w x

structure Procedure {State : Type u} (step : State → PMF State)
    (Input : Type v) (Output : Type w) where
  entry : Input → State
  exit : Input → Output → State
  semantics : Input → PMF Output
  costed : Input → PMF (Output × Nat)
  budget : Input → Nat
  bounded : ∀ input result, result ∈ (costed input).support → result.2 ≤ budget input
  correct : ∀ input, (costed input).map Prod.fst = semantics input
  law : ∀ input horizon, budget input ≤ horizon →
    eval step horizon (entry input) =
      (costed input).bind (fun result => eval step (horizon - result.2) (exit input result.1))

namespace Procedure
variable {State : Type u} {Input : Type v} {Middle : Type w} {Output : Type x}
  {step : State → PMF State}

noncomputable def toBlock (P : Procedure step Input Output) (input : Input) : Block step (P.entry input) where
  budget := P.budget input
  outcome := (P.costed input).map (fun result => (P.exit input result.1, result.2))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨source, hSource, he⟩ := hResult
    subst result
    exact P.bounded input source hSource
  law := by
    intro horizon hBudget
    rw [PMF.bind_map]
    exact P.law input horizon hBudget

theorem result_support (P : Procedure step Input Output) (input : Input) (result : Output × Nat)
    (h : result ∈ (P.costed input).support) : result.1 ∈ (P.semantics input).support := by
  rw [← P.correct, PMF.mem_support_map_iff]
  exact ⟨result, h, rfl⟩

/-- Change the logical input view without changing any executed transition.
The new entry remains a physical precondition; it is not prepared for free. -/
noncomputable def reindex {NewInput : Type w} (P : Procedure step Input Output)
    (view : NewInput → Input) : Procedure step NewInput Output where
  entry := P.entry ∘ view
  exit := fun input => P.exit (view input)
  semantics := P.semantics ∘ view
  costed := P.costed ∘ view
  budget := P.budget ∘ view
  bounded := fun input => P.bounded (view input)
  correct := fun input => P.correct (view input)
  law := fun input => P.law (view input)

/-- Retain the logical input in the output certificate. This changes only
observations; the complete physical exit and cost distribution are preserved. -/
noncomputable def remember (P : Procedure step Input Output) : Procedure step Input (Input × Output) where
  entry := P.entry
  exit := fun _ result => P.exit result.1 result.2
  semantics := fun input => (P.semantics input).map (fun output => (input, output))
  costed := fun input => (P.costed input).map (fun result => ((input, result.1), result.2))
  budget := P.budget
  bounded := by
    intro input result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨source, hSource, he⟩ := hResult
    subst result
    exact P.bounded input source hSource
  correct := by
    intro input
    rw [PMF.map_comp, ← P.correct input, PMF.map_comp]
    rfl
  law := by
    intro input horizon hBudget
    rw [PMF.bind_map]
    exact P.law input horizon hBudget

/-- A full-configuration execution theorem constructs the contract directly.
The residual law continues the original machine after the supplied duration. -/
noncomputable def ofFixed (step : State → PMF State) (entry : Input → State)
    (exit : Input → Output → State) (semantics : Input → PMF Output) (duration : Input → Nat)
    (run : ∀ input, eval step (duration input) (entry input) = (semantics input).map (exit input)) :
    Procedure step Input Output where
  entry := entry
  exit := exit
  semantics := semantics
  costed := fun input => (semantics input).map (fun output => (output, duration input))
  budget := duration
  bounded := by
    intro input result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨output, _, he⟩ := hResult
    subst result
    exact Nat.le_refl _
  correct := by
    intro input
    simp only [PMF.map_comp, Function.comp_def]
    exact PMF.map_id _
  law := by
    intro input horizon hBudget
    conv_lhs => rw [show horizon = duration input + (horizon - duration input) by omega, eval_add, run input]
    simp [PMF.bind_map, Function.comp_def]

/-- Composition charges both procedures. Equal physical handoff states are
required; a nontrivial copy or transfer must be its own charged procedure. -/
noncomputable def seq (first : Procedure step Input Middle) (second : Procedure step Middle Output)
    (handoff : ∀ input middle, middle ∈ (first.semantics input).support →
      second.entry middle = first.exit input middle)
    (cap : Input → Nat)
    (hCap : ∀ input middle, middle ∈ (first.semantics input).support → second.budget middle ≤ cap input) :
    Procedure step Input (Middle × Output) where
  entry := first.entry
  exit := fun _ result => second.exit result.1 result.2
  semantics := fun input => (first.semantics input).bind (fun middle =>
    (second.semantics middle).map (fun output => (middle, output)))
  costed := fun input => (first.costed input).bind (fun middle =>
    (second.costed middle.1).map (fun output => ((middle.1, output.1), middle.2 + output.2)))
  budget := fun input => first.budget input + cap input
  bounded := by
    intro input result hResult
    rw [PMF.mem_support_bind_iff] at hResult
    obtain ⟨middle, hMiddle, hMap⟩ := hResult
    rw [PMF.mem_support_map_iff] at hMap
    obtain ⟨output, hOutput, he⟩ := hMap
    subst result
    have hFirst := first.bounded input middle hMiddle
    have hSecond := second.bounded middle.1 output hOutput
    have hBudget := hCap input middle.1 (first.result_support input middle hMiddle)
    omega
  correct := by
    intro input
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [← first.correct input, PMF.bind_map]
    congr 1
    funext middle
    have h := congrArg (fun p => p.map (fun output => (middle.1, output))) (second.correct middle.1)
    simpa only [PMF.map_comp, Function.comp_def] using h
  law := by
    intro input horizon hHorizon
    rw [first.law input horizon (by omega)]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext middle hMiddle
    rw [← handoff input middle.1 (first.result_support input middle hMiddle)]
    have hFirst := first.bounded input middle hMiddle
    have hBudget := hCap input middle.1 (first.result_support input middle hMiddle)
    simpa only [Nat.sub_sub] using second.law middle.1 (horizon - middle.2) (by omega)

/-- At absorbing final exits, the semantic distribution is the actual whole
machine distribution. Intermediate procedure exits need not be absorbing. -/
theorem final_run (P : Procedure step Input Output) (input : Input)
    (hAbsorbing : ∀ output ∈ (P.semantics input).support,
      step (P.exit input output) = PMF.pure (P.exit input output))
    (horizon : Nat) (hBudget : P.budget input ≤ horizon) :
    eval step horizon (P.entry input) = (P.semantics input).map (P.exit input) := by
  have h := (P.toBlock input).final_law
    (fun result hResult => by
      change result ∈ ((P.costed input).map (fun result => (P.exit input result.1, result.2))).support at hResult
      rw [PMF.mem_support_map_iff] at hResult
      obtain ⟨source, hSource, he⟩ := hResult
      subst result
      exact hAbsorbing source.1 (P.result_support input source hSource)) horizon hBudget
  rw [← P.correct input, PMF.map_comp]
  simpa only [toBlock, PMF.map_comp, Function.comp_def] using h

end Procedure
end Foundation.Probability.TimedExecution
