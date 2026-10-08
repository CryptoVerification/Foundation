import Foundation.Crypto.Semantics.Procedure

/-! Repeated execution contracts pass each actual result to the next round.
Logical observation and budget enlargement preserve the actual cost law;
neither operation adds an uncharged runtime transition. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {State : Type u} {Input : Type v} {Output : Type w} {Observed : Type x}
    {step : State → PMF State}

noncomputable def withBudget (P : Procedure step Input Output) (cap : Input → Nat)
    (hCap : ∀ input, P.budget input ≤ cap input) : Procedure step Input Output where
  entry := P.entry
  exit := P.exit
  semantics := P.semantics
  costed := P.costed
  budget := cap
  bounded := fun input result h => (P.bounded input result h).trans (hCap input)
  correct := P.correct
  law := fun input horizon h => P.law input horizon ((hCap input).trans h)

/-- Change the logical certificate only when the complete physical exit
can still be recovered. Costs and the running machine are preserved. -/
noncomputable def observe (P : Procedure step Input Output) (view : Output → Observed)
    (exit : Input → Observed → State)
    (hExit : ∀ input output, output ∈ (P.semantics input).support → exit input (view output) = P.exit input output) :
    Procedure step Input Observed where
  entry := P.entry
  exit := exit
  semantics := fun input => (P.semantics input).map view
  costed := fun input => (P.costed input).map (fun result => (view result.1, result.2))
  budget := P.budget
  bounded := by
    intro input result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨original, hOriginal, he⟩ := hResult
    subst result
    exact P.bounded input original hOriginal
  correct := by
    intro input
    simp only [PMF.map_comp, Function.comp_def]
    have h := congrArg (fun distribution => distribution.map view) (P.correct input)
    simpa only [PMF.map_comp, Function.comp_def] using h
  law := by
    intro input horizon hBudget
    rw [P.law input horizon hBudget, PMF.bind_map]
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext result hResult
    simp only [Function.comp_def]
    rw [hExit input result.1 (P.result_support input result hResult)]

structure Chain {Value : Type v} (entry : Value → State) (bound : Nat) where
  execution : Procedure step Value Value
  entry_eq : ∀ input, execution.entry input = entry input
  exit_eq : ∀ input output, execution.exit input output = entry output
  budget_eq : ∀ input, execution.budget input = bound

variable (P : Procedure step Input Input) (bound : Nat)
    (hBound : ∀ input, P.budget input ≤ bound)
    (hReturn : ∀ input output, output ∈ (P.semantics input).support → P.exit input output = P.entry output)

noncomputable def iteration : (rounds : Nat) → Chain (step := step) P.entry (rounds * bound)
  | 0 =>
      ⟨Procedure.ofFixed step P.entry (fun _ output => P.entry output) PMF.pure (fun _ => 0)
        (fun _ => by simp [TimedExecution.eval, PMF.pure_map]),
        (fun _ => rfl), (fun _ _ => rfl), (fun _ => by simp [Procedure.ofFixed])⟩
  | rounds + 1 =>
      let previous := iteration rounds
      let first := (P.observe id (fun _ output => P.entry output)
        (fun input output h => (hReturn input output h).symm)).withBudget (fun _ => bound) hBound
      let both := first.seq previous.execution
        (fun _ middle _ => previous.entry_eq middle)
        (fun _ => rounds * bound) (fun _ middle _ => le_of_eq (previous.budget_eq middle))
      let result := both.observe Prod.snd (fun _ output => P.entry output)
        (fun _ output _ => (previous.exit_eq output.1 output.2).symm)
      ⟨result.withBudget (fun _ => (rounds + 1) * bound)
        (fun _ => by change bound + rounds * bound ≤ (rounds + 1) * bound; rw [Nat.add_mul, Nat.one_mul]; omega),
        (fun _ => rfl), (fun _ _ => rfl), (fun _ => rfl)⟩

noncomputable def iterate (rounds : Nat) := (iteration P bound hBound hReturn rounds).execution

theorem iterate_budget (rounds : Nat) (input : Input) :
    (iterate P bound hBound hReturn rounds).budget input = rounds * bound :=
  (iteration P bound hBound hReturn rounds).budget_eq input

theorem iterate_entry (rounds : Nat) (input : Input) :
    (iterate P bound hBound hReturn rounds).entry input = P.entry input :=
  (iteration P bound hBound hReturn rounds).entry_eq input

theorem iterate_exit (rounds : Nat) (input output : Input) :
    (iterate P bound hBound hReturn rounds).exit input output = P.entry output :=
  (iteration P bound hBound hReturn rounds).exit_eq input output

theorem iterate_semantics_zero (input : Input) :
    (iterate P bound hBound hReturn 0).semantics input = PMF.pure input := rfl

theorem iterate_semantics_succ (rounds : Nat) (input : Input) :
    (iterate P bound hBound hReturn (rounds + 1)).semantics input =
      (P.semantics input).bind (fun middle => (iterate P bound hBound hReturn rounds).semantics middle) := by
  simp only [iterate, iteration, withBudget, observe, Procedure.seq, PMF.map_bind,
    PMF.map_comp, Function.comp_def, PMF.map_id, PMF.bind_map]
  rw [show (fun x : Input => x) = id by rfl]
  simp only [PMF.map_id]
theorem iterate_costed_succ (rounds : Nat) (input : Input) :
    (iterate P bound hBound hReturn (rounds + 1)).costed input =
      (P.costed input).bind (fun first =>
        ((iterate P bound hBound hReturn rounds).costed first.1).map
          (fun second => (second.1, first.2 + second.2))) := by
  simp only [iterate, iteration, withBudget, observe, Procedure.seq, PMF.map_bind,
    PMF.map_comp, Function.comp_def, PMF.bind_map]
  rfl
end Foundation.Probability.TimedExecution.Procedure
