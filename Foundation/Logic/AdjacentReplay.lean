import Mathlib.Data.List.Basic

/-! Ordinary adjacent-swap scripts for any Boolean independence relation.
These lemmas do not mention diagrams, probability, or cryptographic games. -/
namespace Foundation.Logic.AdjacentReplay
variable {Letter : Type} (independent : Letter → Letter → Bool)

def swapAt : Nat → List Letter → Option (List Letter)
  | 0, first :: second :: rest => if independent first second then some (second :: first :: rest) else none
  | position + 1, first :: rest => (swapAt position rest).map (first :: ·)
  | _, _ => none

def replay (word : List Letter) : List Nat → Option (List Letter)
  | [] => some word
  | position :: rest => (swapAt independent position word).bind fun middle => replay middle rest

theorem replay_append (first last : List Nat) (word : List Letter) :
    replay independent word (first ++ last) =
      (replay independent word first).bind (fun middle => replay independent middle last) := by
  induction first generalizing word with
  | nil => rfl
  | cons position rest ih => simp [replay, ih, Option.bind_assoc]

theorem replay_cons (action : Letter) (positions : List Nat) (word : List Letter) :
    replay independent (action :: word) (positions.map Nat.succ) =
      (replay independent word positions).map (action :: ·) := by
  induction positions generalizing word with
  | nil => rfl
  | cons position rest ih =>
      cases swapped : swapAt independent position word with
      | none => simp [replay, swapAt, swapped]
      | some middle => simp [replay, swapAt, swapped, ih]

theorem swapAt_inverse (symmetric : ∀ first second, independent first second = independent second first)
    (position : Nat) (word target : List Letter) (checked : swapAt independent position word = some target) :
    swapAt independent position target = some word := by
  induction position generalizing word target with
  | zero =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first rest =>
          cases rest with
          | nil => simp [swapAt] at checked
          | cons second tail =>
              by_cases allowed : independent first second = true
              · simp only [swapAt, allowed, ↓reduceIte, Option.some.injEq] at checked
                subst target
                simp only [swapAt, ← symmetric first second, allowed, ↓reduceIte]
              · simp [swapAt, allowed] at checked
  | succ position ih =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first rest =>
          cases middle : swapAt independent position rest with
          | none => simp [swapAt, middle] at checked
          | some tail =>
              simp only [swapAt, middle, Option.map_some, Option.some.injEq] at checked
              subst target
              simp only [swapAt, ih rest tail middle, Option.map_some]

theorem replay_reverse (symmetric : ∀ first second, independent first second = independent second first)
    (positions : List Nat) (word target : List Letter)
    (checked : replay independent word positions = some target) :
    replay independent target positions.reverse = some word := by
  induction positions generalizing word with
  | nil => simpa only [List.reverse_nil, replay] using checked.symm
  | cons position rest ih =>
      cases first : swapAt independent position word with
      | none => simp [replay, first] at checked
      | some middle =>
          simp only [replay, first, Option.bind_some] at checked
          rw [List.reverse_cons, replay_append, ih middle checked]
          simp only [Option.bind_some, replay, swapAt_inverse independent symmetric position word middle first]

end Foundation.Logic.AdjacentReplay
