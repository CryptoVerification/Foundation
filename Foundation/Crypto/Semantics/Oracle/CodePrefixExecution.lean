import Foundation.Crypto.Semantics.Oracle.HaltReturn

/-! Place a certified active prefix before additional code. The endpoint may
already point into that additional code; no instruction there has yet run. -/
namespace CryptoOracle.Interactive.CodePrefixExecution
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem append_active (source after : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State)
    (active : ∀ result ∈ (TimedExecution.eval (Reification.timedStep source oracle) fuel start).support,
      Reification.terminal result.control = false) :
    TimedExecution.eval (Reification.timedStep (source ++ after) oracle) fuel start =
      TimedExecution.eval (Reification.timedStep source oracle) fuel start := by
  apply HaltReturn.active_eval_of_fetch source (source ++ after) _ oracle fuel start active
  intro pc op fetched _
  have hi : pc < source.length := by
    by_contra hout
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at fetched
    contradiction
  rw [List.getElem?_append_left hi, fetched]

theorem halt_head (tail : Code) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (hpc : machine.pc = 0) (active : machine.halted = false) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host [.native .halt] tail) oracle) 1
      (NativeCode.frame state trace machine) =
      PMF.pure (NativeCode.frame state trace { machine with halted := true }) := by
  simp [CodeRelocation.host, TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, NativeCode.frame, hpc, active,
    Machine.Instruction.next]

theorem host_last_halt (before tail : Code) (positive : 0 < tail.length)
    (last : tail[tail.length - 1]? = some (.native .halt)) :
    (CodeRelocation.host before tail)[(CodeRelocation.host before tail).length - 1]? = some (.native .halt) := by
  rw [CodeRelocation.code_length]
  rw [show before.length + tail.length - 1 = before.length + (tail.length - 1) from by omega,
    CodeRelocation.lookup, last]
  rfl

end CryptoOracle.Interactive.CodePrefixExecution
