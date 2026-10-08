import Foundation.Crypto.Semantics.Machine.BinaryReduction
import Foundation.Crypto.Semantics.Probability.Comp

namespace CryptoLogic.ThreeGames

open Machine Foundation.Probability
open scoped ENNReal

/-- A Boolean challenge experiment with a probabilistic Boolean distinguisher. -/
abbrev Game := Nat → (Bool → ProbComp Bool) → ProbComp Bool

noncomputable def goal (g h : Game) : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Bool → ProbComp Bool
  advantage := fun n _ A => probabilityGap (eventProb (g n A) (· = true))
    (eventProb (h n A) (· = true))

/-- All games expose the same finite challenge/answer protocol. -/
def interface (g h : Game) : MachineAdversaryInterface (goal g h) where
  Request := fun _ _ => Bool
  Response := fun _ _ => Bool
  instanceEncoding := fun _ => FiniteBitEncoding.unit
  requestEncoding := fun _ _ => FiniteBitEncoding.bool
  responseEncoding := fun _ _ => FiniteBitEncoding.bool
  fallback := fun _ _ => false
  assemble := fun _ _ respond => respond

noncomputable def object (g h : Game) : SecurityObject := SecurityObject.ppt (goal g h) (interface g h)

/-- Identity code is a resource-certified branch between experiment pairs.
There is no claim that the new pair alone bounds the old advantage. -/
noncomputable def branch (g h j k : Game) : CertifiedTransform (object g h) (object j k) where
  transform := ⟨fun I => I, fun _ A => A⟩
  compiler := .identity
  budget := fun p => p.budget
  polynomial := fun p => p.polynomial
  halts := fun p => p.halts
  realizes := fun _ _ _ h => h
  admissible := by
    intro F A hA
    obtain ⟨p, q, size, hq, hp, hs, hr⟩ := hA
    exact ⟨p, q, ⟨size.limit, fun n request => size.length_le n request⟩, hq, hp, hs, hr⟩

theorem probabilityGap_triangle (p q r : ℝ≥0∞) :
    probabilityGap p r ≤ probabilityGap p q + probabilityGap q r := by
  apply max_le
  · exact (tsub_le_tsub_add_tsub (a := p) (b := q) (c := r)).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · calc
      r - p ≤ (r - q) + (q - p) := tsub_le_tsub_add_tsub
      _ ≤ probabilityGap q r + probabilityGap p q :=
        add_le_add (le_max_right _ _) (le_max_right _ _)
      _ = probabilityGap p q + probabilityGap q r := add_comm _ _

/-- The concrete two-assumption hybrid step. No independence is needed. -/
noncomputable def reduction (g₀ g₁ g₂ : Game) :
    CertifiedBinaryReduction (object g₀ g₂) (object g₀ g₁) (object g₁ g₂) where
  left := branch g₀ g₂ g₀ g₁
  right := branch g₀ g₂ g₁ g₂
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := fun _ _ _ => probabilityGap_triangle _ _ _

theorem secure (g₀ g₁ g₂ : Game) (F : InstanceFamily (goal g₀ g₂))
    (h₀₁ : (object g₀ g₁).Secure F) (h₁₂ : (object g₁ g₂).Secure F) :
    (object g₀ g₂).Secure F := (reduction g₀ g₁ g₂).secure F h₀₁ h₁₂

end CryptoLogic.ThreeGames
