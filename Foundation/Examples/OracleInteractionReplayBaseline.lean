import Foundation.Examples.OracleInteractionBaseline

/-! A proof-sharing baseline that checks the same adjacent-swap scripts
without constructing or importing higher-dimensional cells. Its inputs are
words and positions, not supplied semantic equalities. -/
namespace CryptoOracle.ProofEdits.Interaction.ReplayBaseline
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input]

def swapAt : Nat → List (Action Input) → Option (List (Action Input))
  | 0, first :: second :: tail =>
      if independent first second then some (second :: first :: tail) else none
  | position + 1, first :: tail => (swapAt position tail).map (first :: ·)
  | _, _ => none

def replay (word : List (Action Input)) : List Nat → Option (List (Action Input))
  | [] => some word
  | position :: rest => do
      let middle ← swapAt position word
      replay middle rest

def validates (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat) : Bool :=
  (scan seen word).isSome && decide (replay word positions = some target)

variable [Fintype Tag] [Nonempty Tag]

theorem swapAt_sound (position : Nat) (word target : List (Action Input))
    (checked : swapAt position word = some target) (state : State Input Tag) : run word state = run target state := by
  induction position generalizing word target state with
  | zero =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases tail with
          | nil => simp [swapAt] at checked
          | cons second tail =>
              by_cases allowed : independent first second = true
              · simp only [swapAt, allowed, ↓reduceIte, Option.some.injEq] at checked
                subst target
                exact Baseline.exchange_context [] tail first second allowed state
              · simp [swapAt, allowed] at checked
  | succ position ih =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases previous : swapAt position tail with
          | none => simp [swapAt, previous] at checked
          | some middle =>
              simp only [swapAt, previous, Option.map_some, Option.some.injEq] at checked
              subst target
              exact congrArg (PMF.bind (step first state)) (funext (ih tail middle previous))

omit [Fintype Tag] [Nonempty Tag] in
theorem swapAt_scan (position : Nat) (word target : List (Action Input))
    (checked : swapAt position word = some target) (seen : Finset Input) : scan seen word = scan seen target := by
  induction position generalizing word target seen with
  | zero =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases tail with
          | nil => simp [swapAt] at checked
          | cons second tail =>
              by_cases allowed : independent first second = true
              · simp only [swapAt, allowed, ↓reduceIte, Option.some.injEq] at checked
                subst target
                exact scan_exchange seen first second tail allowed
              · simp [swapAt, allowed] at checked
  | succ position ih =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases previous : swapAt position tail with
          | none => simp [swapAt, previous] at checked
          | some middle =>
              simp only [swapAt, previous, Option.map_some, Option.some.injEq] at checked
              subst target
              cases first with
              | query message => exact ih tail middle previous (insert message seen)
              | record message => exact ih tail middle previous seen
              | refresh coordinate =>
                  by_cases present : coordinate ∈ seen <;> simp [scan, present, ih tail middle previous seen]

theorem replay_sound (positions : List Nat) (word target : List (Action Input))
    (checked : replay word positions = some target) (state : State Input Tag) : run word state = run target state := by
  induction positions generalizing word with
  | nil => cases checked; rfl
  | cons position rest ih =>
      cases first : swapAt position word with
      | none => simp [replay, first] at checked
      | some middle =>
          simp only [replay, first] at checked
          exact (swapAt_sound position word middle first state).trans (ih middle checked)

omit [Fintype Tag] [Nonempty Tag] in
theorem replay_scan (positions : List Nat) (word target : List (Action Input))
    (checked : replay word positions = some target) (seen : Finset Input) : scan seen word = scan seen target := by
  induction positions generalizing word with
  | nil => cases checked; rfl
  | cons position rest ih =>
      cases first : swapAt position word with
      | none => simp [replay, first] at checked
      | some middle =>
          simp only [replay, first] at checked
          exact (swapAt_scan position word middle first seen).trans (ih middle checked)

theorem validates_kernel (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) (state : State Input Tag) : run word state = run target state := by
  simp only [validates, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact replay_sound positions word target accepted.2 state

theorem validates_invariant (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) (state final : State Input Tag)
    (known : Known seen state) (coherent : Coherent state) (supported : final ∈ (run target state).support) : Coherent final := by
  simp only [validates, Bool.and_eq_true, decide_eq_true_eq] at accepted
  cases source : scan seen word with
  | none => simp [source] at accepted
  | some finalSeen =>
      have targetScan : scan seen target = some finalSeen := (replay_scan positions word target accepted.2 seen).symm.trans source
      exact (run_valid target seen finalSeen targetScan state final known coherent supported).2

/-- Ordinary congruence suffices for any common continuation. -/
theorem validates_continuation {Result : Type} (seen : Finset Input)
    (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true)
    (state : State Input Tag) (next : State Input Tag → PMF Result) :
    (run word state).bind next = (run target state).bind next := by
  rw [validates_kernel seen word target positions accepted state]

/-- Retaining the prefix and its secret does not require a diagram object
for this kernel-equality fragment. -/
theorem validates_joint {Context : Type} (seen : Finset Input)
    (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run word original.2).map (fun final => (original, final))) =
      (prefixLaw.bind fun original => (run target original.2).map (fun final => (original, final))) := by
  simp_rw [validates_kernel seen word target positions accepted]

end CryptoOracle.ProofEdits.Interaction.ReplayBaseline
