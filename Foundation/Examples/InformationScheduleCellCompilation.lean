import Foundation.Logic.AdjacentReplay
import Foundation.Crypto.Logic.Polygraph.InformationScheduleCells
import Foundation.Examples.InformationScheduleBaseline

/-! Every generated visibility/commitment cell compiles to an ordinary
adjacent-swap script with exactly the same number of elementary exchanges.
Conversely, every successful script has a cell of that exchange count. This
compares expanded tree occurrences, NOT shared DAG nodes or proof bytes. -/
namespace CryptoOracle.InformationSchedule.CellCompilation
open Foundation.Probability
namespace R
abbrev replay := @Foundation.Logic.AdjacentReplay.replay
abbrev swapAt := @Foundation.Logic.AdjacentReplay.swapAt
end R
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]
variable (signature : Key → Finset Variable)

theorem independent_symmetric (first second : Action Variable Key) :
    independent signature first second = independent signature second first := by
  cases first <;> cases second <;> simp [independent, ne_comm]

theorem swap_agrees (position : Nat) (word : List (Action Variable Key)) :
    R.swapAt (independent signature) position word = Baseline.swapAt signature position word := by
  induction position generalizing word with
  | zero =>
      cases word with
      | nil => rfl
      | cons first rest => cases rest <;> rfl
  | succ position ih =>
      cases word with
      | nil => rfl
      | cons first rest => simp only [R.swapAt, Foundation.Logic.AdjacentReplay.swapAt, Baseline.swapAt, ih]

theorem replay_agrees (positions : List Nat) (word : List (Action Variable Key)) :
    R.replay (independent signature) word positions = Baseline.replay signature word positions := by
  induction positions generalizing word with
  | nil => rfl
  | cons position rest ih =>
      simp only [R.replay, Foundation.Logic.AdjacentReplay.replay, Baseline.replay, swap_agrees]
      congr 1
      funext middle
      exact ih middle

def script {first second : List (Action Variable Key)} : Cell signature first second → List Nat
  | .refl _ => []
  | .exchange _ _ _ _ => [0]
  | .cons _ cell => (script cell).map Nat.succ
  | .symm cell => (script cell).reverse
  | .trans left right => script left ++ script right

def exchanges {first second : List (Action Variable Key)} : Cell signature first second → Nat
  | .refl _ => 0
  | .exchange _ _ _ _ => 1
  | .cons _ cell => exchanges cell
  | .symm cell => exchanges cell
  | .trans left right => exchanges left + exchanges right

theorem script_length {first second : List (Action Variable Key)} (cell : Cell signature first second) :
    (script signature cell).length = exchanges signature cell := by
  induction cell <;> simp_all [script, exchanges]

theorem compile_sound {first second : List (Action Variable Key)} (cell : Cell signature first second) :
    Baseline.replay signature first (script signature cell) = some second := by
  rw [← replay_agrees]
  induction cell with
  | refl word => rfl
  | exchange first second allowed rest =>
      simp [script, R.replay, Foundation.Logic.AdjacentReplay.replay,
        Foundation.Logic.AdjacentReplay.swapAt, allowed]
  | cons action cell ih =>
      simp only [script, Foundation.Logic.AdjacentReplay.replay_cons, ih, Option.map_some]
  | symm cell ih =>
      exact Foundation.Logic.AdjacentReplay.replay_reverse (independent signature)
        (independent_symmetric signature) _ _ _ ih
  | trans left right ihLeft ihRight =>
      simp only [script, Foundation.Logic.AdjacentReplay.replay_append, ihLeft, Option.bind_some, ihRight]

private theorem swap_has_cell (position : Nat) (first second : List (Action Variable Key))
    (checked : Baseline.swapAt signature position first = some second) :
    ∃ cell : Cell signature first second, exchanges signature cell = 1 := by
  induction position generalizing first second with
  | zero =>
      cases first with
      | nil => simp [Baseline.swapAt] at checked
      | cons first rest =>
          cases rest with
          | nil => simp [Baseline.swapAt] at checked
          | cons next tail =>
              by_cases allowed : independent signature first next = true
              · simp only [Baseline.swapAt, if_pos allowed, Option.some.injEq] at checked
                subst second
                exact ⟨.exchange first next allowed tail, rfl⟩
              · simp [Baseline.swapAt, allowed] at checked
  | succ position ih =>
      cases first with
      | nil => simp [Baseline.swapAt] at checked
      | cons first rest =>
          cases middle : Baseline.swapAt signature position rest with
          | none => simp [Baseline.swapAt, middle] at checked
          | some tail =>
              simp only [Baseline.swapAt, middle, Option.map_some, Option.some.injEq] at checked
              subst second
              obtain ⟨cell, count⟩ := ih rest tail middle
              exact ⟨.cons first cell, count⟩

theorem replay_has_cell (positions : List Nat) (first second : List (Action Variable Key))
    (checked : Baseline.replay signature first positions = some second) :
    ∃ cell : Cell signature first second, exchanges signature cell = positions.length := by
  induction positions generalizing first with
  | nil =>
      simp only [Baseline.replay, Option.some.injEq] at checked
      subst second
      exact ⟨.refl first, rfl⟩
  | cons position rest ih =>
      cases step : Baseline.swapAt signature position first with
      | none => simp [Baseline.replay, step] at checked
      | some middle =>
          simp only [Baseline.replay, step, Option.bind_some] at checked
          obtain ⟨left, leftCount⟩ := swap_has_cell signature position first middle step
          obtain ⟨right, rightCount⟩ := ih middle checked
          exact ⟨.trans left right, by simp only [exchanges, leftCount, rightCount, List.length_cons, Nat.add_comm]⟩

/-- Exact equality of feasible exchange counts, hence also of their minima,
for the whole generated Cell language rather than a selected script family. -/
theorem exchange_costs_iff (first second : List (Action Variable Key)) (count : Nat) :
    (∃ cell : Cell signature first second, exchanges signature cell = count) ↔
      ∃ positions : List Nat, positions.length = count ∧ Baseline.replay signature first positions = some second := by
  constructor
  · rintro ⟨cell, cost⟩
    exact ⟨script signature cell, (script_length signature cell).trans cost, compile_sound signature cell⟩
  · rintro ⟨positions, cost, checked⟩
    obtain ⟨cell, size⟩ := replay_has_cell signature positions first second checked
    exact ⟨cell, size.trans cost⟩

/-- "Optimal" here means fewest elementary exchange occurrences in the
expanded syntax. It is not an optimization of stored proof DAGs. -/
theorem optimal_exchange_cost_iff (first second : List (Action Variable Key)) (count : Nat) :
    ((∃ cell : Cell signature first second, exchanges signature cell = count) ∧
      ∀ cell : Cell signature first second, count ≤ exchanges signature cell) ↔
    ((∃ positions : List Nat, positions.length = count ∧ Baseline.replay signature first positions = some second) ∧
      ∀ positions : List Nat, Baseline.replay signature first positions = some second → count ≤ positions.length) := by
  constructor
  · rintro ⟨feasible, minimal⟩
    refine ⟨(exchange_costs_iff signature first second count).mp feasible, ?_⟩
    intro positions checked
    obtain ⟨cell, cost⟩ := replay_has_cell signature positions first second checked
    simpa only [cost] using minimal cell
  · rintro ⟨feasible, minimal⟩
    refine ⟨(exchange_costs_iff signature first second count).mpr feasible, ?_⟩
    intro cell
    have bound := minimal (script signature cell) (compile_sound signature cell)
    simpa only [script_length] using bound

theorem generated_iff_replay (first second : List (Action Variable Key)) :
    Nonempty (Cell signature first second) ↔
      ∃ positions : List Nat, Baseline.replay signature first positions = some second := by
  constructor
  · rintro ⟨cell⟩
    exact ⟨script signature cell, compile_sound signature cell⟩
  · rintro ⟨positions, checked⟩
    obtain ⟨cell, _⟩ := replay_has_cell signature positions first second checked
    exact ⟨cell⟩

theorem compiled_validates {first second : List (Action Variable Key)} (cell : Cell signature first second)
    (seen : Finset Variable) (available : (scan signature seen first).isSome = true) :
    Baseline.validates signature seen first second (script signature cell) = true := by
  simp [Baseline.validates, available, compile_sound signature cell]

theorem ordinary_joint {Choice Context : Type}
    (policy : (key : Key) → ({v // v ∈ signature key} → Bool) → PMF Choice)
    {first second : List (Action Variable Key)} (cell : Cell signature first second)
    (source : PMF (Context × State Variable Key Choice)) :
    (source.bind fun original => (run signature policy first original.2).map fun final => (original, final)) =
      (source.bind fun original => (run signature policy second original.2).map fun final => (original, final)) := by
  have equality := (Baseline.replay_sound signature policy (script signature cell) first second
    (compile_sound signature cell)).1
  simp_rw [equality]

end CryptoOracle.InformationSchedule.CellCompilation
