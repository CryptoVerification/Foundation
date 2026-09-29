import Foundation.Examples.PolynomialExecutionReduction
import Foundation.Examples.UniformResourceReduction

namespace Foundation.Examples.PolynomialExecutionComposition

open UniformAdversaryModel
open Foundation.Examples.UniformReduction
  (P Q R sourceModel targetModel T)
open Foundation.Examples.UniformResourceReduction
  (S R₂ finalModel T₂)
open Foundation.Examples.PolynomialExecutionReduction
  (sourceDescription sourceCost targetDescription targetCost runtimeBound
    Rpoly Tpoly runtimeBoundPoly)

def finalDescription : finalModel.FiniteDescription where
  encode := fun _ prog => List.replicate (show Nat from prog) true
  encode_injective := by
    intro F p q h
    have hlen := congrArg List.length h
    change (List.replicate (show Nat from p) true).length =
      (List.replicate (show Nat from q) true).length at hlen
    change (show Nat from p) = (show Nat from q)
    rw [List.length_replicate, List.length_replicate] at hlen
    exact hlen

def finalExecution : finalModel.ExecutionSemantics where
  execute := fun _ prog n => (show Nat from prog) + n
  realizes := by
    intro F prog
    rfl

private theorem increment_steps (k : Nat) :
    ExecutionSteps (fun s t : Nat => t = s + 1) k 0 k := by
  induction k with
  | zero => exact ExecutionSteps.zero 0
  | succ k ih => exact ExecutionSteps.succ ih (by rfl)

def finalCost : finalExecution.ExecutionCost where
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

def runtimeBound₂ : T₂.ResourceBound targetCost.toProgramResourceMeasure
    finalCost.toProgramResourceMeasure where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F prog n
    change ((show Nat from prog) + 1) + n ≤
      1 * (n + 1) ^ 0 * ((show Nat from prog) + n + 1) ^ 1
    simp only [one_mul, pow_zero, pow_one]
    omega

example : (Reduction.id P).PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost) :=
  (Reduction.ProgramTransformation.ResourceBound.id P sourceModel
    sourceCost.toProgramResourceMeasure).preservesAdmissibility

example : (Reduction.id P).PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost) :=
  Reduction.id_preservesAdmissibility P _

example : (T.comp T₂).ResourceBound sourceCost.toProgramResourceMeasure
    finalCost.toProgramResourceMeasure :=
  runtimeBound.comp runtimeBound₂

example (F : InstanceFamily P) :
    (T.comp T₂).transform F (3 : Nat) = (5 : Nat) := by rfl

/-- The concrete source witness `3` reaches the target class via the
composed bound; the target program is `5`. -/
example (F : InstanceFamily P) :
    (finalModel.polynomialExecutionClass finalDescription finalCost).admissible
      ((R.comp R₂).mapFamily F)
      ((R.comp R₂).mapAdversaryFamily F
        (sourceModel.realize F (3 : Nat))) := by
  have hSource :
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost).admissible
        F (sourceModel.realize F (3 : Nat)) := by
    refine ⟨(3 : Nat), rfl, ?_⟩
    exact PolynomiallyBounded.add
      (PolynomiallyBounded.const 3) PolynomiallyBounded.id
  exact (runtimeBound.comp runtimeBound₂).preservesAdmissibility.preserves
    F _ hSource

/-- The composed quantitative witness gives class preservation directly. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (finalModel.polynomialExecutionClass finalDescription finalCost) :=
  (runtimeBound.comp runtimeBound₂).preservesAdmissibility

/-- The intermediate class is the same in both sequential steps. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (finalModel.polynomialExecutionClass finalDescription finalCost) :=
  Reduction.comp_preservesAdmissibility R R₂ _ _ _
    runtimeBound.preservesAdmissibility
    runtimeBound₂.preservesAdmissibility

example (F : InstanceFamily P)
    (hS : SecureOnWithin S
      (finalModel.polynomialExecutionClass finalDescription finalCost)
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost) F := by
  have hLoss : (R.comp R₂).loss.PreservesNegligible :=
    AdvantageBound.comp_preservesNegligible R.loss R₂.loss
      AdvantageBound.id_preservesNegligible
      AdvantageBound.id_preservesNegligible
  exact (R.comp R₂).secureOnWithin _ _ F
    (runtimeBound.comp runtimeBound₂).preservesAdmissibility hLoss hS

example (F : InstanceFamily P)
    (hS : SecureOnWithin S
      (finalModel.polynomialExecutionClass finalDescription finalCost)
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost) F := by
  have hQ : SecureOnWithin Q
      (targetModel.polynomialExecutionClass targetDescription targetCost)
      (R.mapFamily F) :=
    R₂.secureOnWithin _ _ (R.mapFamily F)
      runtimeBound₂.preservesAdmissibility
      AdvantageBound.id_preservesNegligible hS
  exact R.secureOnWithin _ _ F runtimeBound.preservesAdmissibility
    AdvantageBound.id_preservesNegligible hQ

/-- A second polynomial advantage loss uses the same adversary and program
maps. The two losses compose independently of the runtime bounds. -/
noncomputable def R₂poly : Reduction Q S where
  mapInstance := fun _ => ()
  reduce := fun _ a => (show Nat from a) + 1
  loss := AdvantageBound.polynomialMultiplier (fun n => n + 1)
  advantage_le := by
    intro _ _ _
    exact zero_le

def T₂poly : R₂poly.ProgramTransformation targetModel finalModel where
  transform := fun _ prog => (show Nat from prog) + 1
  realizes := by
    intro F prog
    funext n
    change ((show Nat from prog) + 1) + n =
      ((show Nat from prog) + n) + 1
    omega

def runtimeBound₂poly : T₂poly.ResourceBound targetCost.toProgramResourceMeasure
    finalCost.toProgramResourceMeasure where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F prog n
    exact runtimeBound₂.bound F prog n

example : (Rpoly.comp R₂poly).PreservesAdmissibility
    (sourceModel.polynomialExecutionClass sourceDescription sourceCost)
    (finalModel.polynomialExecutionClass finalDescription finalCost) :=
  (runtimeBoundPoly.comp runtimeBound₂poly).preservesAdmissibility

example (F : InstanceFamily P)
    (hS : SecureOnWithin S
      (finalModel.polynomialExecutionClass finalDescription finalCost)
      ((Rpoly.comp R₂poly).mapFamily F)) :
    SecureOnWithin P
      (sourceModel.polynomialExecutionClass sourceDescription sourceCost) F := by
  have hFirst : Rpoly.loss.PreservesNegligible :=
    AdvantageBound.polynomialMultiplier_preservesNegligible
      ((PolynomiallyBounded.add PolynomiallyBounded.id
        (PolynomiallyBounded.const 1)).pow 2)
  have hSecond : R₂poly.loss.PreservesNegligible :=
    AdvantageBound.polynomialMultiplier_preservesNegligible
      (PolynomiallyBounded.add PolynomiallyBounded.id
        (PolynomiallyBounded.const 1))
  have hLoss : (Rpoly.comp R₂poly).loss.PreservesNegligible :=
    AdvantageBound.comp_preservesNegligible Rpoly.loss R₂poly.loss
      hFirst hSecond
  exact (Rpoly.comp R₂poly).secureOnWithin _ _ F
    (runtimeBoundPoly.comp runtimeBound₂poly).preservesAdmissibility
    hLoss hS

end Foundation.Examples.PolynomialExecutionComposition
