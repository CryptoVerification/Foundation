import Foundation.Crypto.Semantics.Oracle.ReusableResponseInitialization
import Foundation.Crypto.Semantics.Machine.NativeContinuation

/-! Scheme-independent public machine selection after initialized reusable
execution. The actual caller tapes are exposed; the retained private store,
external state and history are not arguments of native instructions. The
client must still prove that both public tapes contain only permitted data. -/
namespace CryptoOracle.Interactive.ReusableNativeObservation
open Machine Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v}

abbrev RuntimeState := ReusableResponseInitialization.Control Component State

def boundary : RuntimeState (Component := Component) (State := State) → Bool
  | .active (.source _ frame) => match frame.control with
      | .running machine => machine.halted
      | _ => false
  | _ => false

def publicMachine : RuntimeState (Component := Component) (State := State) → Machine.Configuration
  | .active (.source _ frame) => match frame.control with
      | .running machine => machine
      | _ => {}
  | _ => {}

def decision : NativeContinuation.Control (RuntimeState (Component := Component) (State := State)) → Bool
  | .observing _ machine => machine.outputTape.current.getD false
  | _ => false

variable (componentStep : Component → PMF Component)
    (begin : Machine.Tape → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Machine.Tape))
    (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State)

/-- Independent of the generator, handler, oracle, and finite caller code. -/
theorem absorbing (target : RuntimeState (Component := Component) (State := State))
    (h : boundary target = true) :
    ReusableResponseInitialization.step componentStep begin ready generator native code oracle caller target =
      PMF.pure target := by
  cases target with
  | initializing component => simp [boundary] at h
  | aligning tape => simp [boundary] at h
  | active source =>
      cases source with
      | processing => simp [boundary] at h
      | calling => simp [boundary] at h
      | source retained frame =>
          rcases frame with ⟨saved, control, history⟩
          cases control <;> simp only [boundary, Bool.false_eq_true] at h
          rename_i machine
          simp [ReusableResponseInitialization.step, ReusableResponseSource.step,
            Reification.timedStep, Reification.terminal, h, PMF.pure_map]

end CryptoOracle.Interactive.ReusableNativeObservation
