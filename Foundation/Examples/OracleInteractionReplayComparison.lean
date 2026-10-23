import Foundation.Examples.OracleInteractionReplayBaseline
import Foundation.Crypto.Meta.Polygraph.OracleInteractionCertificate

/-! A controlled scope result: erasing cells gives the ordinary replay
checker exactly, so the same scripts have the same acceptance conditions.
This is not a statement about kernel time, proof bytes, or all polygraphs. -/
namespace CryptoOracle.ProofEdits.Interaction.ReplayComparison
variable {Input : Type} [DecidableEq Input]

theorem swapAt_erasure (position : Nat) (word : List (Action Input)) :
    (Certificate.swapAt position word).map Sigma.fst = ReplayBaseline.swapAt position word := by
  induction position generalizing word with
  | zero =>
      cases word with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second tail =>
              by_cases allowed : independent first second = true <;>
                simp [Certificate.swapAt, ReplayBaseline.swapAt, allowed]
  | succ position ih =>
      cases word with
      | nil => rfl
      | cons first tail =>
          simp only [Certificate.swapAt, ReplayBaseline.swapAt, Option.map_map]
          rw [← ih tail, Option.map_map]
          rfl

theorem replay_erasure (positions : List Nat) (word : List (Action Input)) :
    (Certificate.replay word positions).map Sigma.fst = ReplayBaseline.replay word positions := by
  induction positions generalizing word with
  | nil => rfl
  | cons position rest ih =>
      cases first : Certificate.swapAt position word with
      | none =>
          have plain := swapAt_erasure position word
          rw [first] at plain
          simp [Certificate.replay, ReplayBaseline.replay, first, ← plain]
      | some result =>
          obtain ⟨middle, cell⟩ := result
          have plain := swapAt_erasure position word
          rw [first] at plain
          simp only [Certificate.replay, first, ReplayBaseline.replay, ← plain, Option.map_some]
          cases last : Certificate.replay middle rest with
          | none =>
              have restPlain := ih middle
              rw [last] at restPlain
              simp [last, ← restPlain]
          | some result =>
              obtain ⟨final, finalCell⟩ := result
              have restPlain := ih middle
              rw [last] at restPlain
              simp [last, ← restPlain]

/-- Every script, not just the MAC example: identical acceptance with
ordinary shared lemmas, including source freshness rejection. -/
theorem validates_eq (seen : Finset Input) (word target : List (Action Input)) (positions : List Nat) :
    Certificate.validates seen word target positions = ReplayBaseline.validates seen word target positions := by
  have plain := replay_erasure positions word
  cases checked : Certificate.replay word positions with
  | none =>
      rw [checked] at plain
      simp [Certificate.validates, Certificate.certify, ReplayBaseline.validates, checked, ← plain]
  | some result =>
      obtain ⟨endpoint, cell⟩ := result
      rw [checked] at plain
      by_cases same : endpoint = target <;>
        simp [Certificate.validates, Certificate.certify, ReplayBaseline.validates, checked, ← plain, same]

end CryptoOracle.ProofEdits.Interaction.ReplayComparison
