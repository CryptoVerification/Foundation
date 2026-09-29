import Foundation.Assumptions.DDH.Concrete

namespace DDHConcreteExamples

open Foundation.Probability

def toyParams : DDHParameters where
  Element := Bool
  Scalar := Bool
  generator := true
  power := fun _ x => x
  mulScalar := fun x y => x && y
  mul := fun x y => x != y

def toySampling : DDHFiniteSampling toyParams where
  scalarFintype := by change Fintype Bool; infer_instance
  scalarNonempty := by change Nonempty Bool; infer_instance

noncomputable def alwaysTrue : DDHAdversary ProbComp toyParams where
  distinguish := fun _ _ _ => PMF.pure true

example : ddhRealGame toyParams toySampling alwaysTrue = PMF.pure true := by
  simp [ddhRealGame, alwaysTrue, PMF.bind_const]

example : ddhRandomGame toyParams toySampling alwaysTrue = PMF.pure true := by
  simp [ddhRandomGame, alwaysTrue, PMF.bind_const]

example : ddhAdvantage toyParams toySampling alwaysTrue = 0 := by
  simp [ddhAdvantage, ddhRealGame, ddhRandomGame, alwaysTrue,
    eventProb, probabilityGap, PMF.bind_const]

noncomputable example (sampling : (n : Nat) → (params : DDHParameters) →
    Option (DDHFiniteSampling params)) : CryptoGoal :=
  DDH ProbComp (concreteDDHSemantics sampling)

end DDHConcreteExamples
