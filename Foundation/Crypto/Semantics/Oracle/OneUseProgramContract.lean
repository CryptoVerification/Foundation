import Foundation.Crypto.Semantics.Oracle.OneUseSource
import Foundation.Crypto.Semantics.ProcedurePhysical

/-! A completed finite caller contract exposes its complete physical return
and proves an actual caller terminal, independently of its native handler. -/
namespace CryptoOracle.Interactive.OneUseProgramContract
open Foundation.Probability TimedExecution
universe u
variable {State : Type u}

def terminal : OneUseSource.Control State → Bool
  | .source _ _ frame => Reification.terminal frame.control
  | .handling _ _ _ _ _ _ => false

theorem absorbing (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (control : OneUseSource.Control State) (hTerminal : terminal control = true) :
    OneUseSource.step native code oracle control = PMF.pure control := by
  cases control with
  | handling => simp [terminal] at hTerminal
  | source spent store frame =>
      cases hc : frame.control <;>
        simp_all [terminal, OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map]

structure Consumer (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (store : Machine.Tape) where
  execution : Procedure (OneUseSource.step native code oracle) Unit (OneUseSource.Control State)
  entry : execution.entry () = .source false store caller
  exit : ∀ output, execution.exit () output = output
  stops : ∀ output ∈ (execution.semantics ()).support, terminal output = true

end CryptoOracle.Interactive.OneUseProgramContract
