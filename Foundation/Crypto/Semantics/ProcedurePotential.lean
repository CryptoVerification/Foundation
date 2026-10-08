import Foundation.Crypto.Semantics.ExecutionPotential
import Foundation.Crypto.Semantics.ProcedureStage
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Turn invariant-indexed families of existing execution contracts into
whole adaptive executions with a remaining-budget certificate. Only the
states represented by the coordinate type need individual contracts. -/
namespace Foundation.Probability.TimedExecution.Stage.Potential
universe u v
variable {Source : Type u} {Target : Type v} {step : Target → PMF Target}
    (embed : Source → Target) (family : Source → Procedure step Unit Source)
    (hEntry : ∀ source, (family source).entry () = embed source)
    (hExit : ∀ source output, (family source).exit () output = embed output)

noncomputable def next (source : Source) : Stage step embed source :=
  Stage.ofProcedure (Procedure.dispatch family) hEntry hExit source

variable (potential : Source → Nat)
    (hConsume : ∀ source result, result ∈ ((family source).costed ()).support →
      (family source).budget () + potential result.1 ≤ potential source)

noncomputable def whole (count : Nat) : Procedure step Source Source :=
  Stage.procedure (iterate (next embed family hEntry hExit) potential hConsume count)

theorem whole_budget (count : Nat) (start : Source) :
    (whole embed family hEntry hExit potential hConsume count).budget start = potential start :=
  iterate_budget _ potential hConsume count start

theorem whole_semantics (count : Nat) (start : Source) :
    (whole embed family hEntry hExit potential hConsume count).semantics start =
      eval (fun source => (family source).semantics ()) count start :=
  iterate_distribution _ potential hConsume _ (fun source => (family source).correct ()) count start

include hEntry hExit hConsume in
/-- Finite iteration still needs an absorbing exit certificate to become a
whole-machine stopping theorem. Initial potential alone does not prove this. -/
theorem whole_run (count : Nat) (start : Source)
    (hFinal : ∀ final ∈ (eval (fun source => (family source).semantics ()) count start).support,
      step (embed final) = PMF.pure (embed final))
    (horizon : Nat) (hBudget : potential start ≤ horizon) :
    eval step horizon (embed start) =
      (eval (fun source => (family source).semantics ()) count start).map embed :=
  final_run (next embed family hEntry hExit) potential hConsume _ (fun source => (family source).correct ()) count start hFinal horizon hBudget

end Foundation.Probability.TimedExecution.Stage.Potential
