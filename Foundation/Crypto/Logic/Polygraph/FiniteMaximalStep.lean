import Foundation.Crypto.Semantics.Probability.FiniteMaximalKernel
import Foundation.Crypto.Logic.Polygraph.GameCoherenceDiagram

/-! Finite maximal couplings as existing directed game steps. The retained
outcome is the entire supplied finite type; no final bound is a new rule. -/
namespace CryptoLogic.Polygraph.Experiment.FiniteMaximal
open Foundation.Probability Foundation.Probability.FiniteMaximalCoupling
open GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α : Type} [Fintype α]

abbrev game (p : PMF α) (event : α → Prop) : Observed := ⟨α, .sample p, event⟩

def step (p q : PMF α) (event : α → Prop) : Step (game p event) (game q event) where
  kernel := kernel p q
  preserve := kernel_preserve p q
  bad pair := pair.1 ≠ pair.2
  agree x _ y _ good := by
    have same : x = y := not_ne_iff.mp good
    subst y
    rfl
  loss := ENNReal.ofReal (finiteVariation p q)
  bound := by
    change eventProb (p.bind fun x => (kernel p q x).map fun y => (x,y)) _ ≤ _
    rw [kernel_joint, mismatch_probability]

theorem joint_eq (p q : PMF α) (event : α → Prop) :
    (step p q event).joint = joint p q := kernel_joint p q

theorem mismatch_exact (p q : PMF α) (event : α → Prop) :
    eventProb (step p q event).joint (fun pair => pair.1 ≠ pair.2) =
      ENNReal.ofReal (finiteVariation p q) := by
  rw [joint_eq, mismatch_probability]

end
end CryptoLogic.Polygraph.Experiment.FiniteMaximal
