import Foundation.Crypto.Semantics.Oracle.HaltReturn
import Foundation.Crypto.Semantics.Oracle.NativeDeterministicHalt

/-! A checked deterministic suffix can be embedded with its final native
halt replaced by an actual return jump. The source's accepted trace supplies
all fetch obligations; malformed fall-off is never accepted as a return. -/
namespace CryptoOracle.Interactive.NativeDeterministic
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

private theorem next_return (source tail : Code) (machine next : Machine.Configuration)
    (checked : next? source machine = some next) :
    next? (HaltReturn.host source tail) machine =
      some (if next.halted then next.resumeAt source.length else next) := by
  cases active : machine.halted with
  | true => simp [next?, active] at checked
  | false =>
    cases fetched : source[machine.pc]? with
    | none => simp [next?, active, fetched] at checked
    | some op =>
      have inside : machine.pc < source.length := List.getElem?_eq_some_iff.mp fetched |>.1
      have compiled := HaltReturn.source_lookup source tail machine.pc inside
      rw [fetched] at compiled
      cases op with
      | call => simp [next?, active, fetched] at checked
      | native instruction =>
        cases instruction <;>
          simp_all [next?, HaltReturn.instruction, Machine.Instruction.next, Machine.Configuration.resumeAt,
            Machine.Configuration.advance, Machine.Configuration.updateTape, Machine.Configuration.tape]
        all_goals try (split at checked <;> simp_all)
        all_goals subst next; simp_all

theorem finish_return (source tail : Code) (fuel : Nat) (machine final : Machine.Configuration) (ticks : Nat)
    (active : machine.halted = false) (checked : finish source fuel machine = some (final, ticks)) :
    run (HaltReturn.host source tail) ticks machine = some (final.resumeAt source.length) := by
  induction fuel generalizing machine final ticks with
  | zero => simp [finish, active] at checked
  | succ fuel ih =>
    cases head : next? source machine with
    | none => simp [finish, active, head] at checked
    | some middle =>
      have translated := next_return source tail machine middle head
      cases stopped : middle.halted with
      | true =>
        have terminal : finish source fuel middle = some (middle, 0) := by cases fuel <;> simp [finish, stopped]
        have same : (middle, 1) = (final, ticks) := by
          apply Option.some.inj
          simpa only [finish, active, Bool.false_eq_true, if_false, head, Option.bind_some, terminal, Option.map_some, Nat.zero_add] using checked
        cases same
        simp [run, translated, stopped]
      | false =>
        cases rest : finish source fuel middle with
        | none => simp [finish, active, head, rest] at checked
        | some result =>
          obtain ⟨last, used⟩ := result
          have same : (last, used + 1) = (final, ticks) := by simpa [finish, active, head, rest] using checked
          have recursive := ih middle last used stopped rest
          cases same
          simpa only [run, translated, stopped, Bool.false_eq_true, if_false, Option.bind_some] using recursive


theorem run_return (source tail : Code) (ticks : Nat) (machine final : Machine.Configuration)
    (active : machine.halted = false) (halted : final.halted = true)
    (checked : run source ticks machine = some final) :
    run (HaltReturn.host source tail) ticks machine = some (final.resumeAt source.length) := by
  have trace := finish_after_run source ticks 0 machine final checked
  have terminal : finish source 0 final = some (final, 0) := by simp [finish, halted]
  have accepted : finish source ticks machine = some (final, ticks) := by
    simpa only [Nat.add_zero, terminal, Option.map_some] using trace
  exact finish_return source tail ticks machine final ticks active accepted

end CryptoOracle.Interactive.NativeDeterministic
