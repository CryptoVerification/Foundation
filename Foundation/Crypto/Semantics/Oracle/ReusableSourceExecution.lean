import Foundation.Crypto.Semantics.Oracle.ReusableSourceRound
import Foundation.Crypto.Semantics.ProcedureStage

/-! Adaptive whole-caller contracts from certified request rounds. The
coordinate type can carry source layout, size and termination invariants.
Every round receives the actual preceding reply and retained private store.
Finite iteration and genuine completion remain separate proof obligations. -/
namespace CryptoOracle.Interactive.ReusableSourceExecution
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w} {Coordinate : Type x}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

variable (service : ∀ (_retained : Saved) (_caller : Machine.Configuration) (_state : State)
    (_trace : List (List Bool × List Bool)) (_request : List Bool),
    Procedure (outerStep componentStep begin ready native code oracle) Unit
      (ReusableSourceRound.Source (State := State) (Saved := Saved)))
    (hEntry : ∀ retained caller state trace request,
      (service retained caller state trace request).entry () =
        .processing caller state trace request (begin retained request))
    (hExit : ∀ retained caller state trace request output,
      (service retained caller state trace request).exit () output = ReusableSourceRound.embed output)
    (retained : Coordinate → Saved)
    (input : Coordinate → SourcePrefix.Input code oracle)
    (replyCap : Coordinate → SourcePrefix.Input code oracle → Nat)
    (hReplyCap : ∀ coordinate selection frame,
      frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) selection.budget selection.start).support →
      ∀ caller request, frame.control = .awaiting caller request →
        (service (retained coordinate) caller frame.state frame.reverseTrace request).budget () ≤ replyCap coordinate selection)

def embed (coordinate : Coordinate) : ReusableResponseSource.Control Component State Saved :=
  .source (retained coordinate) (input coordinate).start

noncomputable def selected :=
  Procedure.dispatch (fun coordinate =>
    (ReusableSourceRound.round componentStep begin ready native code oracle service hEntry hExit
      (retained coordinate) (replyCap coordinate) (hReplyCap coordinate)).reindex
        (fun _ : Unit => input coordinate))

variable (view : ReusableSourceRound.Source (State := State) (Saved := Saved) → Coordinate)
    (hView : ∀ coordinate output,
      output ∈ ((selected componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap).semantics coordinate).support →
      embed code oracle retained input (view output) = ReusableSourceRound.embed output)

noncomputable def procedure :=
  (selected componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap).observe
    view (fun _ output => embed code oracle retained input output)
    (fun coordinate output h => hView coordinate output h)

theorem budget (coordinate : Coordinate) :
    (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView).budget coordinate =
      (input coordinate).budget + (1 + replyCap coordinate (input coordinate)) := rfl

theorem semantics (coordinate : Coordinate) :
    (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView).semantics coordinate =
      (((ReusableSourceRound.round componentStep begin ready native code oracle service hEntry hExit
        (retained coordinate) (replyCap coordinate) (hReplyCap coordinate)).semantics (input coordinate))).map view := rfl

variable (cap : Nat)
    (hCap : ∀ coordinate, (input coordinate).budget + (1 + replyCap coordinate (input coordinate)) ≤ cap)

noncomputable def whole (count : Nat) :=
  Stage.iterateProcedure
    (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView)
    (fun _ => rfl) (fun _ _ => rfl) cap hCap count

theorem whole_budget (count : Nat) (coordinate : Coordinate) :
    (whole componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView cap hCap count).budget coordinate =
      count * cap :=
  Stage.iteratedProcedure_budget _ cap hCap count coordinate

theorem whole_semantics (count : Nat) (coordinate : Coordinate) :
    (whole componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView cap hCap count).semantics coordinate =
      TimedExecution.eval
        (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate :=
  Stage.iterateProcedure_semantics _ (fun _ => rfl) (fun _ _ => rfl) cap hCap count coordinate

/-- A terminal source frame is physically absorbing; a captured request is
not terminal and cannot be used as a completion witness. -/
theorem terminal_absorbing (coordinate : Coordinate)
    (h : Reification.terminal (input coordinate).start.control = true) :
    outerStep componentStep begin ready native code oracle (embed code oracle retained input coordinate) =
      PMF.pure (embed code oracle retained input coordinate) := by
  cases hc : (input coordinate).start.control <;>
    simp_all [outerStep, embed, ReusableResponseSource.step, Reification.timedStep,
      Reification.terminal, PMF.pure_map]

include hCap in
theorem whole_run (count : Nat) (coordinate : Coordinate)
    (hComplete : ∀ final ∈ (TimedExecution.eval
      (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate).support,
      Reification.terminal (input final).start.control = true)
    (horizon : Nat) (hBudget : count * cap ≤ horizon) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) horizon (embed code oracle retained input coordinate) =
      (TimedExecution.eval
        (procedure componentStep begin ready native code oracle service hEntry hExit retained input replyCap hReplyCap view hView).semantics count coordinate).map
          (embed code oracle retained input) :=
  Stage.iterateProcedure_final _ (fun _ => rfl) (fun _ _ => rfl) cap hCap count coordinate
    (fun final h => terminal_absorbing componentStep begin ready native code oracle retained input final (hComplete final h))
    horizon hBudget

end CryptoOracle.Interactive.ReusableSourceExecution
