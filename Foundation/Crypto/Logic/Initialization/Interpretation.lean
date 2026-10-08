import Foundation.Crypto.Logic.Initialization.Syntax
import Foundation.Crypto.Semantics.InitializedContinuation

/-! Interpret the pure initialization rule using actual sequential contracts.
Physical handoff and local resource bounds are part of each interpretation,
not hidden cryptographic hypotheses or uncharged initialization operations. -/
namespace CryptoLogic.Initialization
open Foundation.Logic Foundation.Probability TimedExecution
universe u v w x y z
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Key : Type w} {Output : Type x}
    {Observed : Type y} (step : State → PMF State)

structure Experiment where
  init : Procedure step Input Key
  continuation : Procedure step Key Output
  handoff : ∀ input key, key ∈ (init.semantics input).support →
    continuation.entry key = init.exit input key
  cap : Input → Nat
  bound : ∀ input key, key ∈ (init.semantics input).support → continuation.budget key ≤ cap input
  view : Key → Output → Observed

namespace Experiment
variable {step}

noncomputable def procedure (E : Experiment (Input := Input) (Key := Key)
    (Output := Output) (Observed := Observed) step) :=
  E.init.seq E.continuation E.handoff E.cap E.bound

noncomputable def publicCost (E : Experiment (Input := Input) (Key := Key)
    (Output := Output) (Observed := Observed) step) (input : Input) :=
  ((E.procedure).costed input).map (fun result => (E.view result.1.1 result.1.2, result.2))

theorem budget (E : Experiment (Input := Input) (Key := Key)
    (Output := Output) (Observed := Observed) step) (input : Input) :
    E.procedure.budget input = E.init.budget input + E.cap input := rfl

end Experiment

variable {step} {RightState : Type z} {RightOutput : Type x} {rightStep : RightState → PMF RightState}
    (left : Experiment (Input := Input) (Key := Key) (Output := Output) (Observed := Observed) step)
    (right : Experiment (Input := Input) (Key := Key) (Output := RightOutput) (Observed := Observed) rightStep)
    (input : Input) (times : PMF Nat) (keysAt : Nat → PMF Key)

noncomputable def model : Model presentation where
  Carrier := fun claim => match claim with
    | .generated =>
        left.init.costed input = times.bind (fun time => (keysAt time).map (fun key => (key, time))) ∧
        right.init.costed input = times.bind (fun time => (keysAt time).map (fun key => (key, time)))
    | .continuation => ∀ time,
        (keysAt time).bind (fun key => (left.continuation.costed key).map
          (fun result => (left.view key result.1, result.2))) =
        (keysAt time).bind (fun key => (right.continuation.costed key).map
          (fun result => (right.view key result.1, result.2)))
    | .experiment leftBudget rightBudget =>
        left.publicCost input = right.publicCost input ∧
        left.procedure.budget input = leftBudget.eval
          (left.init.budget input) (right.init.budget input) (left.cap input) (right.cap input) ∧
        right.procedure.budget input = rightBudget.eval
          (left.init.budget input) (right.init.budget input) (left.cap input) (right.cap input)
  operation := fun _ children =>
    ⟨Procedure.initialized_seq_public_cost_eq left.init right.init left.continuation right.continuation
      left.handoff right.handoff left.cap right.cap left.bound right.bound input times keysAt
      (children 0).1 (children 0).2 left.view right.view (children 1), rfl, rfl⟩

/-- Interpret the same pure proof; cryptographic premises enter only as its
two hypotheses. The result also certifies both composed procedure budgets. -/
theorem sound
    (hGenerated : left.init.costed input =
        times.bind (fun time => (keysAt time).map (fun key => (key, time))) ∧
      right.init.costed input = times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (hSuffix : ∀ time,
      (keysAt time).bind (fun key => (left.continuation.costed key).map
        (fun result => (left.view key result.1, result.2))) =
      (keysAt time).bind (fun key => (right.continuation.costed key).map
        (fun result => (right.view key result.1, result.2)))) :
    left.publicCost input = right.publicCost input ∧
      left.procedure.budget input = left.init.budget input + left.cap input ∧
      right.procedure.budget input = right.init.budget input + right.cap input :=
  proof.eval (Γ := context) (model left right input times keysAt)
    (fun i => by fin_cases i; exact hGenerated; exact hSuffix)

end CryptoLogic.Initialization
