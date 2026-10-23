import Foundation.Examples.InformationScheduleBaseline

/-! Extract local obligations before checking a schedule certificate. Registry
edits only require rechecking obligations whose keys were changed. This module
uses ordinary lists and shared lemmas, with no diagram imports. -/
namespace CryptoOracle.InformationSchedule.LocalRepair
open Foundation.Probability
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]

inductive Check (Variable Key : Type) where
  | available : Key → Finset Variable → Check Variable Key
  | absent : Key → Variable → Check Variable Key
  | fixed : Bool → Check Variable Key

def Check.holds (signature : Key → Finset Variable) : Check Variable Key → Bool
  | .available key seen => decide (signature key ⊆ seen)
  | .absent key input => decide (input ∉ signature key)
  | .fixed result => result

def Check.affected (changed : Finset Key) : Check Variable Key → Bool
  | .available key _ | .absent key _ => decide (key ∈ changed)
  | .fixed _ => false

def exchangeChecks : Action Variable Key → Action Variable Key → List (Check Variable Key)
  | .reveal _, .reveal _ => []
  | .reveal input, .commit key | .commit key, .reveal input => [.absent key input]
  | .commit first, .commit second => [.fixed (decide (first ≠ second))]

theorem exchangeChecks_holds (signature : Key → Finset Variable) (first second : Action Variable Key) :
    (exchangeChecks first second).all (Check.holds signature) = independent signature first second := by
  cases first <;> cases second <;> simp [exchangeChecks, Check.holds, independent]

def sourceChecks (seen : Finset Variable) : List (Action Variable Key) → List (Check Variable Key)
  | [] => []
  | .reveal input :: rest => sourceChecks (insert input seen) rest
  | .commit key :: rest => .available key seen :: sourceChecks seen rest

omit [DecidableEq Key] in
theorem sourceChecks_holds (signature : Key → Finset Variable) (word : List (Action Variable Key))
    (seen : Finset Variable) :
    (sourceChecks seen word).all (Check.holds signature) = (scan signature seen word).isSome := by
  induction word generalizing seen with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | reveal input => exact ih (insert input seen)
      | commit key =>
          by_cases available : signature key ⊆ seen <;>
            simp [sourceChecks, scan, Check.holds, available, ih]

/-- The shape of an exchange script is independent of the registry. -/
def swapPlan : Nat → List (Action Variable Key) → Option (List (Action Variable Key) × List (Check Variable Key))
  | 0, first :: second :: rest => some (second :: first :: rest, exchangeChecks first second)
  | position + 1, first :: rest => (swapPlan position rest).map fun pair => (first :: pair.1, pair.2)
  | _, _ => none

def replayPlan (word : List (Action Variable Key)) : List Nat →
    Option (List (Action Variable Key) × List (Check Variable Key))
  | [] => some (word, [])
  | position :: rest => do
      let first ← swapPlan position word
      let last ← replayPlan first.1 rest
      pure (last.1, first.2 ++ last.2)

def evaluate (signature : Key → Finset Variable)
    (pair : List (Action Variable Key) × List (Check Variable Key)) : Option (List (Action Variable Key)) :=
  if pair.2.all (Check.holds signature) then some pair.1 else none

theorem swapPlan_evaluate (signature : Key → Finset Variable) (position : Nat)
    (word : List (Action Variable Key)) :
    (swapPlan position word).bind (evaluate signature) = Baseline.swapAt signature position word := by
  induction position generalizing word with
  | zero =>
      cases word with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second tail => simp [swapPlan, evaluate, exchangeChecks_holds, Baseline.swapAt]
  | succ position ih =>
      cases word with
      | nil => rfl
      | cons first rest =>
          rw [Baseline.swapAt, ← ih rest]
          cases result : swapPlan position rest with
          | none => simp [swapPlan, result]
          | some pair =>
              by_cases checked : pair.2.all (Check.holds signature) = true <;>
                simp [swapPlan, result, evaluate, checked]

theorem replayPlan_evaluate (signature : Key → Finset Variable) (positions : List Nat)
    (word : List (Action Variable Key)) :
    (replayPlan word positions).bind (evaluate signature) = Baseline.replay signature word positions := by
  induction positions generalizing word with
  | nil => simp [replayPlan, evaluate, Baseline.replay]
  | cons position rest ih =>
      rw [Baseline.replay, ← swapPlan_evaluate]
      cases first : swapPlan position word with
      | none => simp [replayPlan, first]
      | some pair =>
          by_cases c₁ : pair.2.all (Check.holds signature) = true
          · simp only [Option.bind_some, evaluate, if_pos c₁, Option.bind_some]
            rw [← ih pair.1]
            cases last : replayPlan pair.1 rest with
            | none => simp [replayPlan, first, last]
            | some final => simp [replayPlan, first, last, evaluate, List.all_append, c₁]
          · cases last : replayPlan pair.1 rest with
            | none => simp [replayPlan, first, last, evaluate, c₁]
            | some final => simp [replayPlan, first, last, evaluate, List.all_append, c₁]

def compile (seen : Finset Variable) (word : List (Action Variable Key)) (positions : List Nat) :
    Option (List (Action Variable Key) × List (Check Variable Key)) :=
  (replayPlan word positions).map fun pair => (pair.1, sourceChecks seen word ++ pair.2)

theorem compile_validates (signature : Key → Finset Variable) (seen : Finset Variable)
    (word target : List (Action Variable Key)) (positions : List Nat) :
    decide ((compile seen word positions).bind (evaluate signature) = some target) =
      Baseline.validates signature seen word target positions := by
  rw [Baseline.validates, ← replayPlan_evaluate signature positions word,
    ← sourceChecks_holds signature word seen]
  cases result : replayPlan word positions with
  | none => simp [compile, result]
  | some pair =>
      cases src : (sourceChecks seen word).all (Check.holds signature) <;>
        cases dst : pair.2.all (Check.holds signature) <;>
          simp [compile, result, evaluate, List.all_append, src, dst]

theorem Check.unchanged (old new : Key → Finset Variable) (changed : Finset Key)
    (agree : ∀ key ∉ changed, old key = new key) (check : Check Variable Key)
    (unaffected : check.affected changed = false) : check.holds old = check.holds new := by
  cases check with
  | available key seen => simp only [Check.affected, decide_eq_false_iff_not] at unaffected
                          simp [Check.holds, agree key unaffected]
  | absent key input => simp only [Check.affected, decide_eq_false_iff_not] at unaffected
                        simp [Check.holds, agree key unaffected]
  | fixed result => rfl

/-- Exact incremental criterion: all unchanged obligations are discharged by
the old acceptance proof. Only affected obligations require new premises. -/
theorem recheck_iff (old new : Key → Finset Variable) (changed : Finset Key)
    (agree : ∀ key ∉ changed, old key = new key) (checks : List (Check Variable Key))
    (accepted : checks.all (Check.holds old) = true) :
    checks.all (Check.holds new) = true ↔
      (checks.filter (Check.affected changed)).all (Check.holds new) = true := by
  simp only [List.all_eq_true] at accepted ⊢
  constructor
  · intro valid check member
    exact valid check (List.mem_of_mem_filter member)
  · intro valid check member
    cases affected : check.affected changed with
    | false => rw [← Check.unchanged old new changed agree check affected]; exact accepted check member
    | true => exact valid check (List.mem_filter.mpr ⟨member, affected⟩)

theorem compiled_validates_iff (signature : Key → Finset Variable) (seen : Finset Variable)
    (word target : List (Action Variable Key)) (positions : List Nat) (checks : List (Check Variable Key))
    (compiled : compile seen word positions = some (target, checks)) :
    Baseline.validates signature seen word target positions = true ↔ checks.all (Check.holds signature) = true := by
  rw [← compile_validates signature seen word target positions, compiled]
  cases accepted : checks.all (Check.holds signature) <;> simp [evaluate, accepted]

theorem repaired_validates_iff (old new : Key → Finset Variable) (changed : Finset Key)
    (agree : ∀ key ∉ changed, old key = new key) (seen : Finset Variable)
    (word target : List (Action Variable Key)) (positions : List Nat) (checks : List (Check Variable Key))
    (compiled : compile seen word positions = some (target, checks))
    (accepted : Baseline.validates old seen word target positions = true) :
    Baseline.validates new seen word target positions = true ↔
      (checks.filter (Check.affected changed)).all (Check.holds new) = true := by
  rw [compiled_validates_iff new seen word target positions checks compiled]
  exact recheck_iff old new changed agree checks
    ((compiled_validates_iff old seen word target positions checks compiled).mp accepted)

/-- The result concerns equivalence WITHIN the new registry. It does not claim
that changing a policy preserves the old program's distribution. -/
theorem repaired_kernel {Choice : Type} (old new : Key → Finset Variable) (changed : Finset Key)
    (agree : ∀ key ∉ changed, old key = new key) (seen : Finset Variable)
    (word target : List (Action Variable Key)) (positions : List Nat) (checks : List (Check Variable Key))
    (compiled : compile seen word positions = some (target, checks))
    (accepted : Baseline.validates old seen word target positions = true)
    (rechecked : (checks.filter (Check.affected changed)).all (Check.holds new) = true)
    (policy : (key : Key) → ({v // v ∈ new key} → Bool) → PMF Choice) (state : State Variable Key Choice) :
    run new policy word state = run new policy target state := by
  exact Baseline.validated_kernel new policy seen word target positions
    ((repaired_validates_iff old new changed agree seen word target positions checks compiled accepted).mpr rechecked) state

omit [DecidableEq Variable] in
theorem recheck_count_le (changed : Finset Key) (checks : List (Check Variable Key)) :
    (checks.filter (Check.affected changed)).length ≤ checks.length := List.length_filter_le _ _

end CryptoOracle.InformationSchedule.LocalRepair
