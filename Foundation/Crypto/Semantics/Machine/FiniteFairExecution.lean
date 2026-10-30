import Foundation.Crypto.Semantics.Machine.Execution
import Foundation.Crypto.Semantics.Probability.FiniteFairSampling

/-! Any fixed-budget native execution is a deterministic function of at most
one fair bit per step, allowing unused bits. The configuration space itself
need not be finite. Observations inherit the same dyadic realizability. -/
namespace Machine.FiniteFairExecution
open Foundation.Probability FiniteFairSampling
noncomputable section

theorem step_realizable (program : Program) (state : Configuration) :
    Realizable 1 (stepPMF program state) := by
  unfold stepPMF
  cases next program state with
  | none => exact pure 1 _
  | some successor =>
    cases successor with
    | inl target => exact pure 1 _
    | inr targets => exact map bit _

theorem eval_realizable (program : Program) (state : Configuration) (steps : Nat) :
    Realizable steps (evalConfigWithin program state steps) := by
  induction steps with
  | zero => exact pure 0 _
  | succ steps ih =>
    exact bind steps 1 _ (stepPMF program) ih (step_realizable program)

theorem observed_realizable {A : Type} (program : Program) (state : Configuration) (steps : Nat)
    (observe : Configuration → A) : Realizable steps ((evalConfigWithin program state steps).map observe) :=
  map (eval_realizable program state steps) observe

theorem random_initial_realizable (program : Program) (law : PMF Configuration) (n steps : Nat)
    (initial : Realizable n law) : Realizable (n + steps)
      (law.bind (fun state => evalConfigWithin program state steps)) :=
  bind n steps law _ initial (fun state => eval_realizable program state steps)

end
end Machine.FiniteFairExecution
