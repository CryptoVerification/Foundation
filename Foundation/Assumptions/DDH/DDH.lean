import Foundation.Core.Goal
import Foundation.Assumptions.DDH.Basic

open scoped ENNReal

/-- A distinguisher that sees only the three challenge elements.
It lives in `Type 1` to match DDH problem instances in `CryptoGoal`. -/
structure DDHAdversary (M : Type → Type) (params : DDHParameters) : Type 1 where
  distinguish : params.Element → params.Element → params.Element → M Bool

/-- An abstract normalized DDH advantage.

An implementation must sample scalars, form real and random DDH challenges,
run the distinguisher, calculate its distinguishing success, and normalize the
advantage. This interface does not prove that an implementation does so. -/
structure DDHSemantics (M : Type → Type) where
  advantage : (n : Nat) → (params : DDHParameters) → DDHAdversary M params → ℝ≥0∞

/-- DDH as a goal over algebraic problem instances. -/
def DDH (M : Type → Type) (S : DDHSemantics M) : CryptoGoal where
  Instance := fun _ => DDHParameters
  Adversary := fun _ params => DDHAdversary M params
  advantage := fun n params A => S.advantage n params A
