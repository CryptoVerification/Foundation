import Foundation.Examples.UniformReduction
import Foundation.Security.Reduction

namespace Foundation.Examples.UniformResourceReduction

open Foundation.Examples.UniformReduction
  (P Q R sourceModel targetModel T)

/-- A third dummy goal for a two-step reduction chain. -/
def S : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Nat
  advantage := fun _ _ _ => 0

def R₂ : Reduction Q S where
  mapInstance := fun _ => ()
  reduce := fun _ a => (show Nat from a) + 1
  loss := AdvantageBound.id
  advantage_le := by
    intro _ _ _
    exact le_refl _

def finalModel : UniformAdversaryModel S where
  Program := fun _ => Nat
  realize := fun _ prog n => prog + n

def T₂ : R₂.ProgramTransformation targetModel finalModel where
  transform := fun _ prog => (show Nat from prog) + 1
  realizes := by
    intro F prog
    funext n
    change ((show Nat from prog) + 1) + n =
      ((show Nat from prog) + n) + 1
    omega

/-- These synthetic measures observe the natural-number adversary value;
they do not describe execution time or program size. -/
def RP : ResourceMeasure P where
  profile := fun _ A n => A n

def RQ : ResourceMeasure Q where
  profile := fun _ A n => A n

def RS : ResourceMeasure S where
  profile := fun _ A n => A n

/-- Each reduction increments the observed value, so its resource bound
uses `c = 1`, `k = 0`, and `d = 1`. -/
def B₁ : R.ResourceBound RP RQ where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F A n
    change ((show Nat from A n) + 1) ≤
      1 * (n + 1) ^ 0 * ((show Nat from A n) + 1) ^ 1
    simp

def B₂ : R₂.ResourceBound RQ RS where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F A n
    change ((show Nat from A n) + 1) ≤
      1 * (n + 1) ^ 0 * ((show Nat from A n) + 1) ^ 1
    simp

example : (Reduction.id P).ProgramTransformation sourceModel sourceModel :=
  Reduction.ProgramTransformation.id P sourceModel

example (F : InstanceFamily P) (prog : sourceModel.Program F) :
    (Reduction.ProgramTransformation.id P sourceModel).transform F prog = prog := by
  rfl

example : (Reduction.id P).PreservesAdmissibility
    (sourceModel.uniformClass.inter RP.polynomialClass)
    (sourceModel.uniformClass.inter RP.polynomialClass) :=
  (Reduction.ProgramTransformation.id P sourceModel).preservesAdmissibility.inter
    (Reduction.ResourceBound.id P RP).preservesAdmissibility

example : (R.comp R₂).ProgramTransformation sourceModel finalModel :=
  T.comp T₂

example (F : InstanceFamily P) :
    (T.comp T₂).transform F (3 : Nat) = (5 : Nat) := by
  rfl

example (F : InstanceFamily P) (prog : sourceModel.Program F) :
    finalModel.realize ((R.comp R₂).mapFamily F)
      ((T.comp T₂).transform F prog) =
    (R.comp R₂).mapAdversaryFamily F (sourceModel.realize F prog) :=
  (T.comp T₂).realizes F prog

example : (R.comp R₂).ResourceBound RP RS :=
  B₁.comp B₂

/-- The composed witnesses preserve the conjunction of realizability and
polynomial boundedness of the synthetic resource profile. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.uniformClass.inter RP.polynomialClass)
    (finalModel.uniformClass.inter RS.polynomialClass) :=
  (T.comp T₂).preservesAdmissibility.inter
    (B₁.comp B₂).preservesAdmissibility

/-- The sequential route reaches the same combined-class proposition. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.uniformClass.inter RP.polynomialClass)
    (finalModel.uniformClass.inter RS.polynomialClass) := by
  have h₁ : R.PreservesAdmissibility
      (sourceModel.uniformClass.inter RP.polynomialClass)
      (targetModel.uniformClass.inter RQ.polynomialClass) :=
    T.preservesAdmissibility.inter B₁.preservesAdmissibility
  have h₂ : R₂.PreservesAdmissibility
      (targetModel.uniformClass.inter RQ.polynomialClass)
      (finalModel.uniformClass.inter RS.polynomialClass) :=
    T₂.preservesAdmissibility.inter B₂.preservesAdmissibility
  exact Reduction.comp_preservesAdmissibility R R₂ _ _ _ h₁ h₂

/-- Existing security transport accepts the combined-class preservation.
This is an implication for abstract realizability and measured resource. -/
example (F : InstanceFamily P)
    (hS : SecureOnWithin S
      (finalModel.uniformClass.inter RS.polynomialClass)
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P (sourceModel.uniformClass.inter RP.polynomialClass) F := by
  have hLoss : (R.comp R₂).loss.PreservesNegligible :=
    AdvantageBound.comp_preservesNegligible R.loss R₂.loss
      AdvantageBound.id_preservesNegligible
      AdvantageBound.id_preservesNegligible
  exact (R.comp R₂).secureOnWithin _ _ F
    ((T.comp T₂).preservesAdmissibility.inter
      (B₁.comp B₂).preservesAdmissibility)
    hLoss hS

end Foundation.Examples.UniformResourceReduction
