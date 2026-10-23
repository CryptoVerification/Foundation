import Foundation.Crypto.Semantics.Oracle.CodeRelocation
import Foundation.Crypto.Semantics.Oracle.NativeHaltReturnChecked

/-! Relocate accepted deterministic native traces inside an interactive host.
No source fall-off, call or random step can appear in an accepted trace. -/
namespace CryptoOracle.Interactive.NativeDeterministic
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

private theorem next_relocated (before source : Code) (machine : Machine.Configuration) :
    next? (CodeRelocation.host before source) (machine.rebasePc before.length) =
      (next? source machine).map (fun next => next.rebasePc before.length) := by
  cases active : machine.halted with
  | true => simp [next?, Machine.Configuration.rebasePc, active]
  | false =>
    simp only [next?, Machine.Configuration.rebasePc, active, Bool.false_eq_true, if_false]
    rw [CodeRelocation.lookup]
    cases fetched : source[machine.pc]? with
    | none => rfl
    | some instruction =>
      cases instruction with
      | call => rfl
      | native op =>
        simp only [Option.map_some, CodeRelocation.instruction]
        have translated := CodeRelocation.native_next before.length op machine
        simp only [Machine.Configuration.rebasePc, active] at translated
        rw [translated]
        cases op.next machine <;> rfl

theorem run_relocated (before source : Code) (count : Nat) (machine final : Machine.Configuration)
    (checked : run source count machine = some final) :
    run (CodeRelocation.host before source) count (machine.rebasePc before.length) =
      some (final.rebasePc before.length) := by
  induction count generalizing machine with
  | zero => cases checked; rfl
  | succ count ih =>
    cases head : next? source machine with
    | none => simp [run, head] at checked
    | some middle =>
      have tail : run source count middle = some final := by simpa only [run, head, Option.bind_some] using checked
      simpa only [run, next_relocated, head, Option.map_some, Option.bind_some] using ih middle tail


private theorem next_preserved_active (source tail : Code) (machine next : Machine.Configuration)
    (checked : next? source machine = some next) (activeNext : next.halted = false) :
    next? (HaltReturn.host source tail) machine = some next := by
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
      | native op =>
        by_cases halt : op = .halt
        · subst op
          simp [next?, active, fetched, Machine.Instruction.next] at checked
          subst next
          simp at activeNext
        · simp only [Option.map_some, HaltReturn.instruction, halt, if_false] at compiled
          simpa only [next?, active, Bool.false_eq_true, if_false, fetched, compiled] using checked

theorem run_start_active (source : Code) (count : Nat) (machine final : Machine.Configuration)
    (checked : run source count machine = some final) (activeFinal : final.halted = false) : machine.halted = false := by
  cases count with
  | zero => cases checked; exact activeFinal
  | succ count =>
    cases active : machine.halted with
    | false => rfl
    | true => simp [run, next?, active] at checked

theorem run_preserved_active (source tail : Code) (count : Nat) (machine final : Machine.Configuration)
    (checked : run source count machine = some final) (activeFinal : final.halted = false) :
    run (HaltReturn.host source tail) count machine = some final := by
  induction count generalizing machine with
  | zero => exact checked
  | succ count ih =>
    cases head : next? source machine with
    | none => simp [run, head] at checked
    | some middle =>
      have rest : run source count middle = some final := by simpa only [run, head, Option.bind_some] using checked
      have translated := next_preserved_active source tail machine middle head (run_start_active source count middle final rest activeFinal)
      simpa only [run, translated, Option.bind_some] using ih middle rest

end CryptoOracle.Interactive.NativeDeterministic
