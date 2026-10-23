import Foundation.Examples.InformationScheduleCellCompilation
import Foundation.Examples.RandomFunctionMACInformationSchedule

/-! The compilation scope result at the same actual MAC prefix. Redundant
cell trees demonstrate why exchange-occurrence counts are neither optimal
certificate size nor the size of shared source definitions. -/
namespace Foundation.Symmetric.RandomFunctionMACCellCompilation
open Foundation.Probability
open CryptoOracle CryptoOracle.InformationSchedule
open CellCompilation
open RandomFunctionMACInformationSchedule (joint)

def elementary : Cell Example.signature Example.independentBefore Example.independentAfter :=
  .exchange (.commit false) (.reveal false) (by decide) []

theorem ordinary_any_cell {word target : List (Action Bool Bool)} (cell : Cell Example.signature word target) :
    joint word = joint target := by
  have kernel := (Baseline.replay_sound Example.signature Example.policy
    (script Example.signature cell) word target (compile_sound Example.signature cell)).1
  unfold joint
  simp_rw [kernel]

theorem ordinary_any_continuation {Result : Type} {word target : List (Action Bool Bool)}
    (cell : Cell Example.signature word target)
    (next : RandomFunctionMACCausalRepair.PrefixOutcome × InformationSchedule.State Bool Bool Bool → PMF Result) :
    (joint word).bind next = (joint target).bind next := by
  rw [ordinary_any_cell cell]

theorem source_ne_target : Example.independentBefore ≠ Example.independentAfter := by decide

theorem optimal_one :
    (∃ cell : Cell Example.signature Example.independentBefore Example.independentAfter,
      exchanges Example.signature cell = 1) ∧
    ∀ cell : Cell Example.signature Example.independentBefore Example.independentAfter,
      1 ≤ exchanges Example.signature cell := by
  refine ⟨⟨elementary, rfl⟩, ?_⟩
  intro cell
  have length := script_length Example.signature cell
  have checked := compile_sound Example.signature cell
  by_contra small
  have zero : exchanges Example.signature cell = 0 := by omega
  rw [zero] at length
  have empty : script Example.signature cell = [] := List.length_eq_zero_iff.mp length
  rw [empty, Baseline.replay] at checked
  exact source_ne_target (Option.some.inj checked)

theorem ordinary_optimal_one :
    (∃ positions : List Nat, positions.length = 1 ∧
      Baseline.replay Example.signature Example.independentBefore positions = some Example.independentAfter) ∧
    ∀ positions : List Nat,
      Baseline.replay Example.signature Example.independentBefore positions = some Example.independentAfter →
      1 ≤ positions.length :=
  (optimal_exchange_cost_iff Example.signature Example.independentBefore Example.independentAfter 1).mp optimal_one

def loop : Nat → Cell Example.signature Example.independentBefore Example.independentBefore
  | 0 => .trans elementary (.symm elementary)
  | depth + 1 => .trans (loop depth) (loop depth)

def redundant (depth : Nat) : Cell Example.signature Example.independentBefore Example.independentAfter :=
  .trans (loop depth) elementary

theorem loop_exchanges (depth : Nat) : exchanges Example.signature (loop depth) = 2 ^ (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [loop, exchanges, ih, pow_succ, Nat.mul_two]

theorem expanded_compilation_size (depth : Nat) :
    (script Example.signature (redundant depth)).length = 2 ^ (depth + 1) + 1 := by
  rw [script_length]
  simp only [redundant, exchanges, loop_exchanges, elementary]

/-- The shortest ordinary proof is still one exchange for every depth.
The exponential list above belongs to a deliberately redundant input cell. -/
theorem compact_ordinary_alternative (depth : Nat) :
    Baseline.replay Example.signature Example.independentBefore [0] = some Example.independentAfter ∧
      1 < (script Example.signature (redundant depth)).length := by
  constructor
  · exact compile_sound Example.signature elementary
  · rw [expanded_compilation_size]
    have positive : 0 < 2 ^ (depth + 1) := Nat.pow_pos (by omega)
    omega

end Foundation.Symmetric.RandomFunctionMACCellCompilation
