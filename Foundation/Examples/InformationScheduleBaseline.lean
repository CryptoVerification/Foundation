import Foundation.Crypto.Semantics.Oracle.InformationSchedule

/-! Ordinary list replay of dependency-safe exchanges. This baseline imports
no cells or diagram certificates and allows arbitrary shared local lemmas. -/
namespace CryptoOracle.InformationSchedule.Baseline
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]
variable (signature : Key → Finset Variable)

def swapAt : Nat → List (Action Variable Key) → Option (List (Action Variable Key))
  | 0, first :: second :: rest =>
      if independent signature first second = true then some (second :: first :: rest) else none
  | position + 1, first :: rest => (swapAt position rest).map (first :: ·)
  | _, _ => none

def replay (word : List (Action Variable Key)) : List Nat → Option (List (Action Variable Key))
  | [] => some word
  | position :: rest => (swapAt signature position word).bind fun middle => replay middle rest

def validates (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat) : Bool :=
  (scan signature seen word).isSome && decide (replay signature word positions = some target)

variable {Choice : Type} (policy : (key : Key) → ({v // v ∈ signature key} → Bool) → PMF Choice)

theorem swap_sound (position : Nat) (word target : List (Action Variable Key))
    (checked : swapAt signature position word = some target) :
    (∀ state : State Variable Key Choice, run signature policy word state = run signature policy target state) ∧
    (∀ seen, scan signature seen word = scan signature seen target) := by
  induction position generalizing word target with
  | zero =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases tail with
          | nil => simp [swapAt] at checked
          | cons second rest =>
              by_cases allowed : independent signature first second = true
              · simp only [swapAt, if_pos allowed, Option.some.injEq] at checked
                subst target
                refine ⟨?_, fun seen => scan_exchange signature seen first second allowed rest⟩
                intro state
                change (step signature policy first state).bind
                  (fun next => (step signature policy second next).bind (run signature policy rest)) = _
                rw [← PMF.bind_bind, step_exchange signature policy first second allowed]
                exact PMF.bind_bind _ _ _
              · simp [swapAt, allowed] at checked
  | succ position ih =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first rest =>
          cases middle : swapAt signature position rest with
          | none => simp [swapAt, middle] at checked
          | some tail =>
              simp only [swapAt, middle, Option.map_some, Option.some.injEq] at checked
              subst target
              obtain ⟨kernel, availability⟩ := ih rest tail middle
              refine ⟨?_, ?_⟩
              · intro state
                exact congrArg (PMF.bind (step signature policy first state)) (funext kernel)
              · intro seen
                cases first with
                | reveal input => exact availability (insert input seen)
                | commit key => by_cases available : signature key ⊆ seen <;>
                    simp [scan, available, availability seen]

theorem replay_sound (positions : List Nat) (word target : List (Action Variable Key))
    (checked : replay signature word positions = some target) :
    (∀ state : State Variable Key Choice, run signature policy word state = run signature policy target state) ∧
    (∀ seen, scan signature seen word = scan signature seen target) := by
  induction positions generalizing word target with
  | nil => simp only [replay, Option.some.injEq] at checked; subst target; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons position rest ih =>
      cases middle : swapAt signature position word with
      | none => simp [replay, middle] at checked
      | some tail =>
          simp only [replay, middle, Option.bind_some] at checked
          obtain ⟨firstKernel, firstScan⟩ := swap_sound signature policy position word tail middle
          obtain ⟨lastKernel, lastScan⟩ := ih tail target checked
          exact ⟨fun state => (firstKernel state).trans (lastKernel state),
            fun seen => (firstScan seen).trans (lastScan seen)⟩

theorem validated_kernel (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat)
    (accepted : validates signature seen word target positions = true) (state : State Variable Key Choice) :
    run signature policy word state = run signature policy target state := by
  simp only [validates, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have checked : replay signature word positions = some target := accepted.2
  exact (replay_sound signature policy positions word target checked).1 state

end CryptoOracle.InformationSchedule.Baseline
