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

/-- Interpreter exits are distinct from native halted machine frames. A
certified execution ending in a machine frame cannot have fetched past the
source block, even if it already executed a native halt. -/
def exited (control : Control) : Bool :=
  match control with
  | .finished _ => true
  | _ => false

theorem append_step_of_no_exit (source after : Code) (oracle : BitOracle State)
    (start : Configuration State)
    (nextActive : ∀ out ∈ (Reification.timedStep source oracle start).support, exited out.control = false) :
    Reification.timedStep (source ++ after) oracle start = Reification.timedStep source oracle start := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      by_cases hh : machine.halted = true
      · simp [Reification.timedStep, Reification.terminal, hh]
      · have ha : machine.halted = false := by simpa using hh
        cases hf : source[machine.pc]? with
        | none =>
            have hs : (⟨state, .finished false, trace⟩ : Configuration State) ∈
                (Reification.timedStep source oracle ⟨state, .running machine, trace⟩).support := by
              simp [Reification.timedStep, Reification.terminal, ha, Reification.perform,
                Reification.action, transition, hf]
            have hb := nextActive _ hs
            contradiction
        | some op =>
            have hi : machine.pc < source.length := (List.getElem?_eq_some_iff.mp hf).1
            have hg : (source ++ after)[machine.pc]? = some op := by rw [List.getElem?_append_left hi, hf]
            simp [Reification.timedStep, Reification.terminal, ha, Reification.perform,
              Reification.action, transition, hf, hg]
  | sending => rfl
  | reversing => rfl
  | awaiting => rfl
  | loading => rfl
  | advancing => rfl
  | rewinding => rfl
  | finished => rfl

theorem append_running_final (source after : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State)
    (final : ∀ out ∈ (TimedExecution.eval (Reification.timedStep source oracle) fuel start).support,
      exited out.control = false) :
    TimedExecution.eval (Reification.timedStep (source ++ after) oracle) fuel start =
      TimedExecution.eval (Reification.timedStep source oracle) fuel start := by
  apply eval_congr_of_active_final _ _ (fun frame => exited frame.control) _ _ fuel start final
  · intro frame he
    rcases frame with ⟨state, control, trace⟩
    cases control <;> simp_all [exited, Reification.timedStep, Reification.terminal]
  · intro frame _ hn
    exact append_step_of_no_exit source after oracle frame hn

end CryptoOracle.Interactive.CodePrefixExecution
