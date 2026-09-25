import Foundation.Core.Goal
import Foundation.Notions.PKE.Basic

open scoped ENNReal

/-- A two-stage IND-CPA adversary with its own state type. -/
structure INDCPAAdversary (M : Type → Type) (scheme : PKE M) where
  State : Type
  choose : scheme.PublicKey → M (scheme.Message × scheme.Message × State)
  guess : State → scheme.Ciphertext → M Bool

/-- The chosen experiment assigns an already-normalized advantage. -/
structure INDCPASemantics (M : Type → Type) where
  advantage : (n : Nat) → (scheme : PKE M) → INDCPAAdversary M scheme → ℝ≥0∞

/-- IND-CPA as a goal over PKE instances at each security parameter. -/
def INDCPA (M : Type → Type) (S : INDCPASemantics M) : CryptoGoal where
  Instance := fun _ => PKE M
  Adversary := fun _ scheme => INDCPAAdversary M scheme
  advantage := fun n scheme A => S.advantage n scheme A
