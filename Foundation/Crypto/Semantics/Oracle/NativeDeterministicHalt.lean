import Foundation.Crypto.Semantics.Oracle.NativeDeterministic

/-! A checked deterministic suffix with genuine first native halt. Fuel
exhaustion is rejected; the returned duration excludes padding after halt.
The original timed semantics may then pad only at its actual terminal state.
-/
namespace CryptoOracle.Interactive.NativeDeterministic
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def finish (code : Code) : Nat → Machine.Configuration → Option (Machine.Configuration × Nat)
  | fuel, machine => if machine.halted then some (machine, 0) else match fuel with
    | 0 => none
    | count + 1 => (next? code machine).bind fun middle =>
        (finish code count middle).map (fun final => (final.1, final.2 + 1))

theorem finish_spec (code : Code) (fuel : Nat) (machine final : Machine.Configuration) (ticks : Nat)
    (checked : finish code fuel machine = some (final, ticks)) :
    final.halted = true ∧ ticks ≤ fuel ∧ run code ticks machine = some final := by
  induction fuel generalizing machine final ticks with
  | zero =>
      cases halted : machine.halted with
      | false => simp [finish, halted] at checked
      | true =>
          have same : (machine, 0) = (final, ticks) := by simpa [finish, halted] using checked
          cases same
          exact ⟨halted, Nat.le_refl _, rfl⟩
  | succ fuel ih =>
      cases halted : machine.halted with
      | true =>
          have same : (machine, 0) = (final, ticks) := by simpa [finish, halted] using checked
          cases same
          exact ⟨halted, Nat.zero_le _, rfl⟩
      | false =>
          cases first : next? code machine with
          | none => simp [finish, halted, first] at checked
          | some middle =>
              cases tail : finish code fuel middle with
              | none => simp [finish, halted, first, tail] at checked
              | some result =>
                  have same : (result.1, result.2 + 1) = (final, ticks) := by
                    simpa [finish, halted, first, tail] using checked
                  rcases result with ⟨last, used⟩
                  cases same
                  obtain ⟨stopped, bound, executed⟩ := ih middle last used tail
                  refine ⟨stopped, by omega, ?_⟩
                  simpa only [run, first, Option.bind_some] using executed

/-- Extend a successful native prefix by a checked halting suffix. Accepted
prefixes cannot contain an earlier halt because `run` rejects such padding. -/
theorem finish_after_run (code : Code) (first rest : Nat) (machine middle : Machine.Configuration)
    (checkedPrefix : run code first machine = some middle) :
    finish code (first + rest) machine =
      (finish code rest middle).map (fun final => (final.1, first + final.2)) := by
  induction first generalizing machine with
  | zero =>
      have same : machine = middle := Option.some.inj checkedPrefix
      subst machine
      simp
  | succ first ih =>
      cases head : next? code machine with
      | none => simp [run, head] at checkedPrefix
      | some next =>
          have active : machine.halted = false := by
            cases h : machine.halted with
            | false => rfl
            | true => simp [next?, h] at head
          have tail : run code first next = some middle := by
            simpa only [run, head, Option.bind_some] using checkedPrefix
          simp only [Nat.succ_add, finish, active, Bool.false_eq_true, if_false, head, Option.bind_some]
          rw [ih next tail, Option.map_map]
          congr 1

/-- Every later horizon observes the same halted physical frame, including
the caller's work memory, private oracle state and prior transcript. -/
theorem finish_timed {State : Type} (code : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (fuel : Nat)
    (machine final : Machine.Configuration) (ticks : Nat)
    (checked : finish code fuel machine = some (final, ticks))
    (horizon : Nat) (enough : ticks ≤ horizon) :
    TimedExecution.eval (Reification.timedStep code oracle) horizon
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running final, trace⟩ := by
  obtain ⟨halted, _, executed⟩ := finish_spec code fuel machine final ticks checked
  rw [show horizon = ticks + (horizon - ticks) by omega, TimedExecution.eval_add,
    run_sound code oracle state trace ticks machine final executed, PMF.pure_bind,
    Reification.timed_eval_eq]
  exact Reification.eval_terminal code oracle _ _ halted

end CryptoOracle.Interactive.NativeDeterministic
