import Foundation.Crypto.Semantics.Oracle.OneUseSourceInterval

/-! A real caller halt is one charged instruction, with the entire private
store, caller tapes and actual transcript retained in the absorbing exit. -/
namespace CryptoOracle.Interactive.OneUseSourceHalt
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (store : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool))

def final : OneUseSource.Control State :=
  .source spent store ⟨state, .running { machine with halted := true }, trace⟩

variable (hActive : machine.halted = false) (hHalt : code[machine.pc]? = some (.native .halt))

noncomputable def halt : Procedure (OneUseSource.step native code oracle) Unit (OneUseSource.Control State) :=
  Procedure.ofFixed _
    (fun _ => .source spent store ⟨state, .running machine, trace⟩)
    (fun _ output => output) (fun _ => PMF.pure (final spent store machine state trace)) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
        hActive, Reification.perform, Reification.action, transition, hHalt,
        Machine.Instruction.next, final, PMF.pure_map])

theorem absorbing : OneUseSource.step native code oracle (final spent store machine state trace) =
    PMF.pure (final spent store machine state trace) := by
  simp [final, OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map]

end CryptoOracle.Interactive.OneUseSourceHalt
