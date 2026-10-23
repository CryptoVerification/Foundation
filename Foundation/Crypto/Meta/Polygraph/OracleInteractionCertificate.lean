import Foundation.Crypto.Logic.Polygraph.OracleInteractionCells

/-! Replay mixed diagrams only when the adjacent actions are syntactically
independent. Validation additionally scans exposed coordinates in the source.
Cell.scan then transfers the same exposure specification to the target.
-/
namespace CryptoOracle.ProofEdits.Interaction.Certificate
variable {Input : Type} [DecidableEq Input]

def swapAt : Nat → (word : List (Action Input)) → Option (Σ target, Cell word target)
  | 0, first :: second :: tail =>
      if allowed : independent first second = true then
        some ⟨second :: first :: tail, .exchange first second allowed tail⟩
      else none
  | position + 1, first :: tail => (swapAt position tail).map fun result =>
      ⟨first :: result.1, .cons first result.2⟩
  | _, _ => none

def replay (word : List (Action Input)) : List Nat → Option (Σ target, Cell word target)
  | [] => some ⟨word, .refl word⟩
  | position :: rest => do
      let first ← swapAt position word
      let last ← replay first.1 rest
      pure ⟨last.1, .trans first.2 last.2⟩

def certify (word target : List (Action Input)) (positions : List Nat) : Option (Cell word target) :=
  match replay word positions with
  | none => none
  | some result => if same : result.1 = target then some (same ▸ result.2) else none

def validates (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat) : Bool :=
  (scan seen word).isSome && (certify word target positions).isSome

theorem validates_sound (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) :
    ∃ finalSeen, ∃ _cell : Cell word target, scan seen word = some finalSeen ∧ scan seen target = some finalSeen := by
  cases planned : scan seen word with
  | none => simp [validates, planned] at accepted
  | some finalSeen =>
      cases checked : certify word target positions with
      | none => simp [validates, checked] at accepted
      | some cell => exact ⟨finalSeen, cell, rfl, (cell.scan seen).symm.trans planned⟩

theorem rejects_invalid_source (seen : Finset Input) (word target : List (Action Input))
    (positions : List Nat) (invalid : scan seen word = none) :
    validates seen word target positions = false := by simp [validates, invalid]

theorem rejects_exposed_refresh (seen : Finset Input) (message : Input)
    (target : List (Action Input)) (positions : List Nat) :
    validates seen [.query message, .refresh message] target positions = false := by
  apply rejects_invalid_source
  simp [scan]

theorem validates_kernel {Tag : Type} [Fintype Tag] [Nonempty Tag]
    (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) (state : State Input Tag) :
    run word state = run target state := by
  obtain ⟨_, cell, _, _⟩ := validates_sound seen word target positions accepted
  exact cell.sound state

theorem validates_invariant {Tag : Type} [Fintype Tag] [Nonempty Tag]
    (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat)
    (accepted : validates seen word target positions = true) (state final : State Input Tag)
    (known : Known seen state) (coherent : Coherent state) (supported : final ∈ (run target state).support) :
    Coherent final := by
  obtain ⟨finalSeen, _, _, valid⟩ := validates_sound seen word target positions accepted
  exact (run_valid target seen finalSeen valid state final known coherent supported).2

end CryptoOracle.ProofEdits.Interaction.Certificate
