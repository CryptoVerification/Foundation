import Foundation.Resource.PolynomialExecution
import Foundation.Resource.ProgramReduction
import Foundation.Examples.PolynomialExecution
import Foundation.Examples.UniformReduction
import Foundation.Security.Reduction

namespace Foundation.Examples.PolynomialExecutionReduction

open UniformAdversaryModel
open Foundation.Examples.UniformReduction
  (P Q R sourceModel targetModel T)
open Foundation.Examples.FiniteProgram
  (description)
open Foundation.Examples.ExecutionSemantics
  (execution)
open Foundation.Examples.ExecutionCost
  (toyCost)

universe u v a b x y

/-- The existing resource-bound preservation theorem has exactly the
polynomial-execution-class type when both measures come from validated runs.
The target witness is `T.transform F prog`; the target description witness is
model-level data and needs no separate program choice. -/
example {PS : CryptoGoal.{u}} {QT : CryptoGoal.{v}}
    {R₀ : Reduction PS QT}
    {MP : UniformAdversaryModel.{u, a} PS}
    {MQ : UniformAdversaryModel.{v, b} QT}
    {T₀ : R₀.ProgramTransformation MP MQ}
    (DP : MP.FiniteDescription) (DQ : MQ.FiniteDescription)
    {EP : MP.ExecutionSemantics} {EQ : MQ.ExecutionSemantics}
    {CP : EP.ExecutionCost.{u, a, x}}
    {CQ : EQ.ExecutionCost.{v, b, y}}
    (B : T₀.ResourceBound CP.toProgramResourceMeasure
      CQ.toProgramResourceMeasure) :
    R₀.PreservesAdmissibility
      (MP.polynomialExecutionClass DP CP)
      (MQ.polynomialExecutionClass DQ CQ) :=
  B.preservesAdmissibility

/-- The source goal and model have the same definitions as the earlier
Nat-program example, so its description and run can be reused. -/
def sourceDescription : sourceModel.FiniteDescription := description
def sourceExecution : sourceModel.ExecutionSemantics := execution
def sourceCost : sourceExecution.ExecutionCost := toyCost

def targetDescription : targetModel.FiniteDescription where
  encode := fun _ prog => List.replicate (show Nat from prog) true
  encode_injective := by
    intro F p q h
    have hlen := congrArg List.length h
    change (List.replicate (show Nat from p) true).length =
      (List.replicate (show Nat from q) true).length at hlen
    change (show Nat from p) = (show Nat from q)
    rw [List.length_replicate, List.length_replicate] at hlen
    exact hlen

def targetExecution : targetModel.ExecutionSemantics where
  execute := fun _ prog n => (show Nat from prog) + n
  realizes := by
    intro F prog
    rfl

private theorem increment_steps (k : Nat) :
    ExecutionSteps (fun s t : Nat => t = s + 1) k 0 k := by
  induction k with
  | zero => exact ExecutionSteps.zero 0
  | succ k ih => exact ExecutionSteps.succ ih (by rfl)

def targetCost : targetExecution.ExecutionCost where
  State := fun _ _ _ => Nat
  initial := fun _ _ _ => 0
  step := fun _ _ _ s t => t = s + 1
  final := fun _ prog n => (show Nat from prog) + n
  runtime := fun _ prog n => (show Nat from prog) + n
  output := fun _ _ _ s => s
  valid := by
    intro F prog n
    exact increment_steps _
  output_eq := by
    intro F prog n
    rfl

/-- Incrementing the program increases the validated toy run by one step. -/
def runtimeBound : T.ResourceBound sourceCost.toProgramResourceMeasure
    targetCost.toProgramResourceMeasure where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F prog n
    change ((show Nat from prog) + 1) + n ≤
      1 * (n + 1) ^ 0 * ((show Nat from prog) + n + 1) ^ 1
    simp only [one_mul, pow_zero, one_mul, pow_one]
    omega

example : R.PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (targetModel.polynomialExecutionClass targetDescription targetCost) :=
  runtimeBound.preservesAdmissibility

example (F : InstanceFamily P)
    (hQ : SecureOnWithin Q
      (targetModel.polynomialExecutionClass targetDescription targetCost)
      (R.mapFamily F)) :
    SecureOnWithin P
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost) F := by
  exact R.secureOnWithin _ _ F runtimeBound.preservesAdmissibility
    AdvantageBound.id_preservesNegligible hQ

/-- The same dummy adversary map can carry a non-identity polynomial
advantage loss. This changes neither program execution nor its run length. -/
noncomputable def Rpoly : Reduction P Q where
  mapInstance := fun _ => true
  reduce := fun _ a => (show Nat from a) + 1
  loss := AdvantageBound.polynomialMultiplier (fun n => (n + 1) ^ 2)
  advantage_le := by
    intro _ _ _
    exact zero_le

def Tpoly : Rpoly.ProgramTransformation sourceModel targetModel where
  transform := fun _ prog => (show Nat from prog) + 1
  realizes := by
    intro F prog
    funext n
    change ((show Nat from prog) + 1) + n =
      ((show Nat from prog) + n) + 1
    omega

def runtimeBoundPoly : Tpoly.ResourceBound sourceCost.toProgramResourceMeasure
    targetCost.toProgramResourceMeasure where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F prog n
    exact runtimeBound.bound F prog n

private theorem factor_polynomiallyBounded :
    PolynomiallyBounded (fun n => (n + 1) ^ 2) := by
  exact (PolynomiallyBounded.add PolynomiallyBounded.id
    (PolynomiallyBounded.const 1)).pow 2

example (F : InstanceFamily P)
    (hQ : SecureOnWithin Q
      (targetModel.polynomialExecutionClass targetDescription targetCost)
      (Rpoly.mapFamily F)) :
    SecureOnWithin P
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost) F := by
  exact Rpoly.secureOnWithin _ _ F runtimeBoundPoly.preservesAdmissibility
    (AdvantageBound.polynomialMultiplier_preservesNegligible factor_polynomiallyBounded)
    hQ

end Foundation.Examples.PolynomialExecutionReduction
