import Foundation.Logic.Polygraph.StructuralCartesianRootAnnotationLinear
import Foundation.Examples.MixedCircuitExpansionCriticalWirePass

/-! A complete scalar discrepancy profile for the selected first atomic
projection of the actual canonical tensor example. All annotations in the
restricted class preserving the new 31-form basis give equal values here.
This does NOT construct a higher comparison or prove tensor coherence. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionAnnotationProfile
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Cartesian.Higher
attribute [local instance] CoherenceInvariant.weightGroup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def scalarProfile (index : Fin 18) : Int :=
  match index.val with
  | 0 => -4
  | 1 => 2
  | 3 => 4
  | 5 => -2
  | 7 | 8 => 2
  | 9 | 14 => 1
  | _ => 0

private theorem basis_0 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (0 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (0 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 0) := by rfl

private theorem basis_1 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (1 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (1 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 1) := by rfl

private theorem basis_2 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (2 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (2 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 2) := by rfl

private theorem basis_3 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (3 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (3 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 3) := by rfl

private theorem basis_4 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (4 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (4 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 4) := by rfl

private theorem basis_5 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (5 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (5 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 5) := by rfl

private theorem basis_6 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (6 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (6 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 6) := by rfl

private theorem basis_7 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (7 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (7 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 7) := by rfl

private theorem basis_8 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (8 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (8 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 8) := by rfl

private theorem basis_9 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (9 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (9 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 9) := by rfl

private theorem basis_10 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (10 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (10 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 10) := by rfl

private theorem basis_11 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (11 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (11 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 11) := by rfl

private theorem basis_12 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (12 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (12 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 12) := by rfl

private theorem basis_13 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (13 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (13 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 13) := by rfl

private theorem basis_14 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (14 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (14 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 14) := by rfl

private theorem basis_15 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (15 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (15 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 15) := by rfl

private theorem basis_16 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (16 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (16 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 16) := by rfl

private theorem basis_17 : @Eq Int
    (RootAnnotation.trackWeight (Pi.single (17 : Fin 18) 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single (17 : Fin 18) 1) TensorObservation.obstructedSecond)
    (scalarProfile 17) := by rfl

theorem basis_profile (index : Fin 18) : @Eq Int
    (RootAnnotation.trackWeight (Pi.single index 1) TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight (Pi.single index 1) TensorObservation.obstructedSecond)
    (scalarProfile index) := by
  fin_cases index
  · exact basis_0
  · exact basis_1
  · exact basis_2
  · exact basis_3
  · exact basis_4
  · exact basis_5
  · exact basis_6
  · exact basis_7
  · exact basis_8
  · exact basis_9
  · exact basis_10
  · exact basis_11
  · exact basis_12
  · exact basis_13
  · exact basis_14
  · exact basis_15
  · exact basis_16
  · exact basis_17

theorem discrepancy (coeff : Fin 18 → Int) : @Eq Int
    (RootAnnotation.trackWeight coeff TensorObservation.obstructedFirst -
      RootAnnotation.trackWeight coeff TensorObservation.obstructedSecond)
    (-4 * coeff 0 + 2 * coeff 1 + 4 * coeff 3 - 2 * coeff 5 +
      2 * coeff 7 + 2 * coeff 8 + coeff 9 + coeff 14) := by
  rw [RootAnnotation.Linear.profile coeff TensorObservation.obstructedFirst,
    RootAnnotation.Linear.profile coeff TensorObservation.obstructedSecond,
    ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub, basis_profile]
  norm_num [Fin.sum_univ_succ, scalarProfile, zsmul_eq_mul]
  change -(coeff 0 * 4) + (coeff 1 * 2 + (coeff 3 * 4 + (-(coeff 5 * 2) +
    (coeff 7 * 2 + (coeff 8 * 2 + (coeff 9 + coeff 14)))))) = _
  ring

theorem admissible_scalar_equality (coeff : Fin 18 → Int) (valid : ExpansionCritical.Annotation.Admissible coeff) :
    RootAnnotation.trackWeight coeff TensorObservation.obstructedFirst =
      RootAnnotation.trackWeight coeff TensorObservation.obstructedSecond := by
  change @Eq Int (RootAnnotation.trackWeight coeff TensorObservation.obstructedFirst)
    (RootAnnotation.trackWeight coeff TensorObservation.obstructedSecond)
  apply sub_eq_zero.mp
  rw [discrepancy]
  have assoc := valid.assoc
  have fst := valid.fst
  have distribution := valid.distribution
  have tensor := valid.tensor
  have rightUnit := valid.rightUnit
  omega

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.ExpansionAnnotationProfile
