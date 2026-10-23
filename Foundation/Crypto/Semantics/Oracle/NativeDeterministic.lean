import Foundation.Crypto.Semantics.Oracle.ReificationExecution

/-! Check deterministic native segments of an actual mixed oracle program.
The checker rejects calls, random instructions, missing code and padding after
halt. Its soundness theorem relates the original interactive timed transition
system, with arbitrary private oracle state and transcript, to every accepted
segment. Running the checker is proof construction, not a runtime primitive.
-/
namespace CryptoOracle.Interactive.NativeDeterministic
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
universe u

def next? (code : Code) (machine : Machine.Configuration) : Option Machine.Configuration :=
  if machine.halted then none else
    match code[machine.pc]? with
    | some (.native instruction) => match instruction.next machine with
      | .inl next => some next
      | .inr _ => none
    | _ => none

def run (code : Code) : Nat → Machine.Configuration → Option Machine.Configuration
  | 0, machine => some machine
  | count + 1, machine => (next? code machine).bind (run code count)

theorem run_add (code : Code) (first second : Nat) (machine : Machine.Configuration) :
    run code (first + second) machine = (run code first machine).bind (run code second) := by
  induction first generalizing machine with
  | zero => simp [run]
  | succ first ih =>
      simp only [Nat.succ_add, run, Option.bind_assoc]
      congr 1
      funext middle
      exact ih middle

theorem next_sound {State : Type u} (code : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (machine final : Machine.Configuration) (checked : next? code machine = some final) :
    Reification.timedStep code oracle ⟨state, .running machine, trace⟩ =
      PMF.pure ⟨state, .running final, trace⟩ := by
  cases active : machine.halted with
  | true => simp [next?, active] at checked
  | false =>
      cases fetched : code[machine.pc]? with
      | none => simp [next?, active, fetched] at checked
      | some instruction =>
          cases instruction with
          | call => simp [next?, active, fetched] at checked
          | native instruction =>
              cases successor : instruction.next machine with
              | inr pair => simp [next?, active, fetched, successor] at checked
              | inl next =>
                  have same : next = final := by simpa [next?, active, fetched, successor] using checked
                  subst final
                  simp [Reification.timedStep, Reification.terminal, Reification.perform,
                    Reification.action, transition, active, fetched, successor]

theorem run_sound {State : Type u} (code : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (count : Nat)
    (machine final : Machine.Configuration) (checked : run code count machine = some final) :
    TimedExecution.eval (Reification.timedStep code oracle) count ⟨state, .running machine, trace⟩ =
      PMF.pure ⟨state, .running final, trace⟩ := by
  induction count generalizing machine with
  | zero =>
      have same : machine = final := Option.some.inj checked
      subst final
      rfl
  | succ count ih =>
      cases hn : next? code machine with
      | none => simp [run, hn] at checked
      | some middle =>
          have tail : run code count middle = some final := by simpa only [run, hn, Option.bind_some] using checked
          rw [TimedExecution.eval, next_sound code oracle state trace machine middle hn, PMF.pure_bind]
          exact ih middle tail

end CryptoOracle.Interactive.NativeDeterministic
