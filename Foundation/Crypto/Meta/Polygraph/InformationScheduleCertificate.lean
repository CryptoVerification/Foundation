import Foundation.Crypto.Logic.Polygraph.InformationScheduleCells

/-! Replay dependency-safe swaps and retain their generated cells. Validation
checks source availability and obtains target availability by Cell.scan. -/
namespace CryptoOracle.InformationSchedule.Certificate
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]
variable (signature : Key → Finset Variable)

def swapAt : Nat → (word : List (Action Variable Key)) → Option (Σ target, Cell signature word target)
  | 0, first :: second :: rest =>
      if allowed : independent signature first second = true then
        some ⟨second :: first :: rest, .exchange first second allowed rest⟩
      else none
  | position + 1, first :: rest => (swapAt position rest).map fun result =>
      ⟨first :: result.1, .cons first result.2⟩
  | _, _ => none

def replay (word : List (Action Variable Key)) : List Nat → Option (Σ target, Cell signature word target)
  | [] => some ⟨word, .refl word⟩
  | position :: rest => do
      let middle ← swapAt signature position word
      let last ← replay middle.1 rest
      pure ⟨last.1, .trans middle.2 last.2⟩

def certify (word target : List (Action Variable Key)) (positions : List Nat) : Option (Cell signature word target) :=
  match replay signature word positions with
  | none => none
  | some result => if same : result.1 = target then some (same ▸ result.2) else none

def validates (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat) : Bool :=
  (scan signature seen word).isSome && (certify signature word target positions).isSome

theorem validates_sound (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat)
    (accepted : validates signature seen word target positions = true) :
    ∃ available, ∃ _cell : Cell signature word target,
      scan signature seen word = some available ∧ scan signature seen target = some available := by
  cases source : scan signature seen word with
  | none => simp [validates, source] at accepted
  | some available =>
      cases checked : certify signature word target positions with
      | none => simp [validates, checked] at accepted
      | some cell => exact ⟨available, cell, rfl, (Cell.scan signature cell seen).symm.trans source⟩

variable {Choice : Type} (policy : (key : Key) → ({v // v ∈ signature key} → Bool) → PMF Choice)

theorem validates_kernel (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat)
    (accepted : validates signature seen word target positions = true) (state : State Variable Key Choice) :
    run signature policy word state = run signature policy target state := by
  obtain ⟨_, cell, _, _⟩ := validates_sound signature seen word target positions accepted
  exact Cell.sound signature policy cell state

theorem validates_final_seen (seen : Finset Variable) (word target : List (Action Variable Key))
    (positions : List Nat) (accepted : validates signature seen word target positions = true)
    (state final : State Variable Key Choice) (matchesSeen : state.seen = seen)
    (supported : final ∈ (run signature policy target state).support) :
    ∃ available, scan signature seen word = some available ∧ final.seen = available := by
  obtain ⟨available, _, source, destination⟩ := validates_sound signature seen word target positions accepted
  refine ⟨available, source, ?_⟩
  apply run_seen signature policy target state final available _ supported
  rwa [matchesSeen]

theorem rejects_unavailable (seen : Finset Variable) (key : Key) (rest : List (Action Variable Key))
    (missing : ¬ signature key ⊆ seen) (target : List (Action Variable Key)) (positions : List Nat) :
    validates signature seen (.commit key :: rest) target positions = false := by
  simp [validates, scan, missing]

theorem rejects_invalid_target (seen : Finset Variable) (word target : List (Action Variable Key))
    (positions : List Nat) (invalid : scan signature seen target = none) :
    validates signature seen word target positions = false := by
  cases accepted : validates signature seen word target positions with
  | false => rfl
  | true =>
      obtain ⟨_, _, _, destination⟩ := validates_sound signature seen word target positions accepted
      rw [invalid] at destination
      contradiction

end CryptoOracle.InformationSchedule.Certificate
