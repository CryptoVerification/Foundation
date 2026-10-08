import Foundation.Crypto.Logic.General.Execution

/-! Register an observed native experiment against a cryptographic goal.
Concrete adapters supply execution/resource predicates and exact game laws;
this interface does not assign a cost to arbitrary host computations. Finite
code remains in the code system, while runtime evidence remains in resources. -/
namespace CryptoLogic.General
open Foundation.Probability
open scoped ENNReal
universe u v
set_option backward.isDefEq.respectTransparency false

structure ObservedExecution (K : CodeSystem) (m : K.Machine) (P : CryptoGoal.{u}) where
  Resources : Type v
  ExecutesWithin : InstanceFamily P → K.Code m → Resources → Prop
  game : InstanceFamily P → K.Code m → Resources → Nat → Bool → PMF Bool
  modelGame : ∀ F, AdversaryFamily P F → Nat → Bool → PMF Bool
  advantage_eq : ∀ F A n, advantageProfile P F A n =
    probabilityGap (eventProb (modelGame F A n false) (· = true))
      (eventProb (modelGame F A n true) (· = true))

namespace ObservedExecution
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (B : ObservedExecution.{u, v} K m P)

def Realizes (F : InstanceFamily P) (A : AdversaryFamily P F) (code : K.Code m) (r : B.Resources) : Prop :=
  ∀ n side, B.game F code r n side = B.modelGame F A n side

def interface : ExecutionInterface K m P where
  Resources := B.Resources
  ExecutesWithin := B.ExecutesWithin
  Realizes := B.Realizes

def object : SecurityObject K m where
  goal := P
  execution := B.interface
  adversaries := { admissible := fun F A =>
    ∃ code r, B.ExecutesWithin F code r ∧ B.Realizes F A code r }
  represented := by intro F A h; exact h

noncomputable def nativeAdvantage (F : InstanceFamily P) (code : K.Code m) (r : B.Resources) (n : Nat) :=
  probabilityGap (eventProb (B.game F code r n false) (· = true))
    (eventProb (B.game F code r n true) (· = true))

theorem realizes_advantage (F A) (code : K.Code m) (r : B.Resources)
    (h : B.Realizes F A code r) (n : Nat) :
    advantageProfile P F A n = B.nativeAdvantage F code r n := by
  rw [B.advantage_eq, ← h n false, ← h n true]
  rfl

theorem witness_game (F A) (W : B.object.Witness F A) (n : Nat) (side : Bool) :
    B.game F W.code W.resources n side = B.modelGame F A n side := W.realizes n side

/-- Security for the represented native programs transfers to the goal.
The represented class includes execution evidence and game realization. -/
theorem secure_of_native (F : InstanceFamily P)
    (h : ∀ code r, B.ExecutesWithin F code r → Negligible (B.nativeAdvantage F code r)) :
    B.object.Secure F := by
  intro A hA
  obtain ⟨code, r, hExec, hReal⟩ := hA
  have hn := h code r hExec
  have he : advantageProfile P F A = B.nativeAdvantage F code r :=
    funext (B.realizes_advantage F A code r hReal)
  change Negligible (advantageProfile P F A)
  rw [he]
  exact hn

/-- A quantitative bound is preserved for every represented source attack;
it is not itself a proof that the bound holds for a concrete cryptosystem. -/
theorem advantage_le (F A) (W : B.object.Witness F A) (epsilon : Nat → ℝ≥0∞)
    (h : ∀ code r, B.ExecutesWithin F code r → ∀ n, B.nativeAdvantage F code r n ≤ epsilon n)
    (n : Nat) : advantageProfile P F A n ≤ epsilon n := by
  rw [B.realizes_advantage F A W.code W.resources W.realizes]
  exact h W.code W.resources W.executes n

end ObservedExecution
end CryptoLogic.General
