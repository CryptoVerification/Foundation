import Foundation.Logic.Polygraph.StructuralCartesianExpansionAnnotation
import Mathlib.Algebra.BigOperators.Pi
/-! The routed root annotation is additive in the eighteen coefficients.
Its value is determined by eighteen unit-coordinate profiles. This is an
ordinary additive decomposition, not a higher coherence or cost theorem. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation.Linear
open CoherenceInvariant
variable {Atom : Type}
attribute [local instance] CoherenceInvariant.weightGroup

theorem step_zero {a b : Shape Atom} {p q : Wire a b} (step : Step p q) :
    stepWeight 0 step = (0 : Weight b) := by
  induction step with
  | root root => exact constant_zero _
  | seqLeft child fixed ih => rw [stepWeight, ih, eval_zero]
  | seqRight fixed child ih => exact ih
  | tensorLeft child fixed ih => simp only [stepWeight, ih]; rfl
  | tensorRight fixed child ih => simp only [stepWeight, ih]; rfl

theorem step_add (left right : Fin 18 → Int) {a b : Shape Atom} {p q : Wire a b} (step : Step p q) :
    stepWeight (left + right) step = stepWeight left step + stepWeight right step := by
  induction step with
  | root root => exact ExpansionCritical.Annotation.constant_add _ _ _
  | seqLeft child fixed ih => rw [stepWeight, ih, eval_add]; rfl
  | seqRight fixed child ih => exact ih
  | tensorLeft child fixed ih => simp only [stepWeight, ih, Prod.mk_add_mk, add_zero]
  | tensorRight fixed child ih => simp only [stepWeight, ih, Prod.mk_add_mk, add_zero]

theorem track_zero {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    trackWeight 0 path = (0 : Weight b) := by
  induction path with
  | refl => rfl
  | step step => exact step_zero step
  | comp one two ih₁ ih₂ => simp only [trackWeight, ih₁, ih₂, add_zero]
  | inv child ih => simp only [trackWeight, ih, neg_zero]

theorem track_add (left right : Fin 18 → Int) {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    trackWeight (left + right) path = trackWeight left path + trackWeight right path := by
  induction path with
  | refl => simp only [trackWeight, add_zero]
  | step step => exact step_add left right step
  | comp one two ih₁ ih₂ => simp only [trackWeight, ih₁, ih₂]; abel
  | inv child ih => simp only [trackWeight, ih]; abel

def annotationHom {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) : (Fin 18 → Int) →+ Weight b where
  toFun := fun coeff => trackWeight coeff path
  map_zero' := track_zero path
  map_add' := fun left right => track_add left right path

theorem profile (coeff : Fin 18 → Int) {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    trackWeight coeff path = ∑ i : Fin 18, coeff i • trackWeight (Pi.single i 1) path := by
  change annotationHom path coeff = _
  conv_lhs => rw [← Finset.univ_sum_single coeff]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i member
  have single : (Pi.single i (coeff i) : Fin 18 → Int) = coeff i • (Pi.single i (1 : Int) : Fin 18 → Int) := by
    ext j
    by_cases same : i = j
    · subst j; simp
    · simp [same]
  rw [single, map_zsmul]
  rfl
end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.RootAnnotation.Linear
