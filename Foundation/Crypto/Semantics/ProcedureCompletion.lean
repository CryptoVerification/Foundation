import Foundation.Crypto.Semantics.ProcedureIteration

/-! A completed operational contract records genuine terminal exits.
Its logical result is the complete physical configuration. It can be formed
from any existing procedure without padding or changing its actual costs. -/
namespace Foundation.Probability.TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

structure Completion {State : Type u} (step : State → PMF State)
    (start : State) (terminal : State → Prop) where
  execution : Procedure step Unit State
  entry : execution.entry () = start
  exit : ∀ output, execution.exit () output = output
  stopped : ∀ output ∈ (execution.semantics ()).support, terminal output

namespace Completion
variable {State : Type u} {Output : Type v} {step : State → PMF State}
    {start : State} {terminal : State → Prop}

noncomputable def ofProcedure (P : Procedure step Unit Output)
    (hEntry : P.entry () = start)
    (hStopped : ∀ output ∈ (P.semantics ()).support, terminal (P.exit () output)) :
    Completion step start terminal where
  execution := P.observe (P.exit ()) (fun _ output => output)
    (by intro argument output _; cases argument; rfl)
  entry := hEntry
  exit := fun _ => rfl
  stopped := by
    intro output h
    change output ∈ ((P.semantics ()).map (P.exit ())).support at h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨original, ho, rfl⟩ := h
    exact hStopped original ho

variable (C : Completion step start terminal)
    (hAbsorb : ∀ state, terminal state → step state = PMF.pure state)

include hAbsorb in
theorem final_run (horizon : Nat) (hBudget : C.execution.budget () ≤ horizon) :
    eval step horizon start = C.execution.semantics () := by
  have h := C.execution.final_run ()
    (fun output ho => by rw [C.exit]; exact hAbsorb output (C.stopped output ho)) horizon hBudget
  rw [C.entry] at h
  have he : C.execution.exit () = id := funext C.exit
  rw [he, PMF.map_id] at h
  exact h

theorem ofProcedure_budget (P : Procedure step Unit Output)
    (hEntry : P.entry () = start)
    (hStopped : ∀ output ∈ (P.semantics ()).support, terminal (P.exit () output)) :
    (ofProcedure P hEntry hStopped).execution.budget () = P.budget () := rfl

theorem ofProcedure_semantics (P : Procedure step Unit Output)
    (hEntry : P.entry () = start)
    (hStopped : ∀ output ∈ (P.semantics ()).support, terminal (P.exit () output)) :
    (ofProcedure P hEntry hStopped).execution.semantics () = (P.semantics ()).map (P.exit ()) := rfl

theorem ofProcedure_costed (P : Procedure step Unit Output)
    (hEntry : P.entry () = start)
    (hStopped : ∀ output ∈ (P.semantics ()).support, terminal (P.exit () output)) :
    (ofProcedure P hEntry hStopped).execution.costed () =
      (P.costed ()).map (fun result => (P.exit () result.1, result.2)) := rfl

end Completion
end Foundation.Probability.TimedExecution
