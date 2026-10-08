import Foundation.Crypto.Semantics.Oracle.CallerRound
import Foundation.Crypto.Semantics.ProcedureStage

/-! Response-independent whole-caller contracts from certified request rounds. The
coordinate type can carry source layout, size and termination invariants.
Every round receives the actual preceding reply and retained private store.
Finite iteration and genuine completion remain separate proof obligations. -/
namespace CryptoOracle.Interactive.CallerExecution
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Saved : Type v} {Target : Type w} {Coordinate : Type x}
    {code : Code} {oracle : BitOracle State} (R : CallerRuntime.Runtime Saved Target code oracle)

variable (service : ∀ (_retained : Saved) (_caller : Machine.Configuration) (_state : State)
    (_trace : List (List Bool × List Bool)) (_request : List Bool),
    Procedure R.step Unit
      (CallerRuntime.Runtime.Source (State := State) (Saved := Saved)))
    (hEntry : ∀ retained caller state trace request,
      (service retained caller state trace request).entry () =
        R.request retained caller state trace request)
    (hExit : ∀ retained caller state trace request output,
      (service retained caller state trace request).exit () output = R.source output)
    (retained : Coordinate → Saved)
    (input : Coordinate → SourcePrefix.Input code oracle)
    (replyCap : Coordinate → SourcePrefix.Input code oracle → Nat)
    (hReplyCap : ∀ coordinate selection frame,
      frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) selection.budget selection.start).support →
      ∀ caller request, frame.control = .awaiting caller request →
        (service (retained coordinate) caller frame.state frame.reverseTrace request).budget () ≤ replyCap coordinate selection)

def embed (coordinate : Coordinate) : Target :=
  R.embed (retained coordinate) (input coordinate).start

noncomputable def selected :=
  Procedure.dispatch (fun coordinate =>
    (R.round service hEntry hExit
      (retained coordinate) (replyCap coordinate) (hReplyCap coordinate)).reindex
        (fun _ : Unit => input coordinate))

variable (view : CallerRuntime.Runtime.Source (State := State) (Saved := Saved) → Coordinate)
    (hView : ∀ coordinate output,
      output ∈ ((selected R service hEntry hExit retained input replyCap hReplyCap).semantics coordinate).support →
      embed R retained input (view output) = R.source output)

noncomputable def procedure :=
  (selected R service hEntry hExit retained input replyCap hReplyCap).observe
    view (fun _ output => embed R retained input output)
    (fun coordinate output h => hView coordinate output h)

theorem budget (coordinate : Coordinate) :
    (procedure R service hEntry hExit retained input replyCap hReplyCap view hView).budget coordinate =
      (input coordinate).budget + (1 + replyCap coordinate (input coordinate)) := rfl

theorem semantics (coordinate : Coordinate) :
    (procedure R service hEntry hExit retained input replyCap hReplyCap view hView).semantics coordinate =
      (((R.round service hEntry hExit
        (retained coordinate) (replyCap coordinate) (hReplyCap coordinate)).semantics (input coordinate))).map view := rfl

variable (cap : Nat)
    (hCap : ∀ coordinate, (input coordinate).budget + (1 + replyCap coordinate (input coordinate)) ≤ cap)

noncomputable def whole (count : Nat) :=
  Stage.iterateProcedure
    (procedure R service hEntry hExit retained input replyCap hReplyCap view hView)
    (fun _ => rfl) (fun _ _ => rfl) cap hCap count

theorem whole_budget (count : Nat) (coordinate : Coordinate) :
    (whole R service hEntry hExit retained input replyCap hReplyCap view hView cap hCap count).budget coordinate =
      count * cap :=
  Stage.iteratedProcedure_budget _ cap hCap count coordinate

theorem whole_semantics (count : Nat) (coordinate : Coordinate) :
    (whole R service hEntry hExit retained input replyCap hReplyCap view hView cap hCap count).semantics coordinate =
      TimedExecution.eval
        (procedure R service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate :=
  Stage.iterateProcedure_semantics _ (fun _ => rfl) (fun _ _ => rfl) cap hCap count coordinate

/-- A terminal source frame is physically absorbing; a captured request is
not terminal and cannot be used as a completion witness. -/
theorem terminal_absorbing (coordinate : Coordinate)
    (h : Reification.terminal (input coordinate).start.control = true) :
    R.step (embed R retained input coordinate) =
      PMF.pure (embed R retained input coordinate) := R.terminal (retained coordinate) (input coordinate).start h

include hCap in
theorem whole_run (count : Nat) (coordinate : Coordinate)
    (hComplete : ∀ final ∈ (TimedExecution.eval
      (procedure R service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate).support,
      Reification.terminal (input final).start.control = true)
    (horizon : Nat) (hBudget : count * cap ≤ horizon) :
    TimedExecution.eval (R.step) horizon (embed R retained input coordinate) =
      (TimedExecution.eval
        (procedure R service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate).map
          (embed R retained input) :=
  Stage.iterateProcedure_final _ (fun _ => rfl) (fun _ _ => rfl) cap hCap count coordinate
    (fun final h => terminal_absorbing R retained input final (hComplete final h))
    horizon hBudget

end CryptoOracle.Interactive.CallerExecution
