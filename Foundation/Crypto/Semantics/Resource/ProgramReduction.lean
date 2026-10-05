import Foundation.Crypto.Semantics.Resource.ProgramMeasure
import Foundation.Crypto.Semantics.Resource.UniformReduction
import Foundation.Crypto.Semantics.Resource.PolynomialBound

universe u v w a b c

namespace Reduction.ProgramTransformation

/-- A pointwise bound on the resource of the specific program produced by
`T.transform`. This measures program objects, rather than adversary families. -/
structure ResourceBound {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    (T : R.ProgramTransformation MP MQ)
    (CP : ProgramResourceMeasure MP)
    (CQ : ProgramResourceMeasure MQ) where
  coefficient : Nat
  securityDegree : Nat
  sourceDegree : Nat
  bound : ∀ (F : InstanceFamily P) (prog : MP.Program F) (n : Nat),
    CQ.profile (R.mapFamily F) (T.transform F prog) n ≤
      coefficient * (n + 1) ^ securityDegree *
        (CP.profile F prog n + 1) ^ sourceDegree

namespace ResourceBound

/-- The identity program transformation preserves a program's resource up to
`s ≤ s + 1`. -/
def id (P : CryptoGoal.{u}) (M : UniformAdversaryModel.{u, a} P)
    (C : ProgramResourceMeasure M) :
    (ProgramTransformation.id P M).ResourceBound C C where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F prog n
    change C.profile F prog n ≤
      1 * (n + 1) ^ 0 * (C.profile F prog n + 1) ^ 1
    simp

/-- Compose bounds along `P → Q → S`, measuring the intermediate program
`T₁.transform F prog`. The resulting metadata is
`c = c₂ * (c₁ + 1)^d₂`, `k = k₂ + k₁ * d₂`, and `d = d₁ * d₂`. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    {R₁ : Reduction P Q} {R₂ : Reduction Q S}
    {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    {MS : UniformAdversaryModel.{w, c} S}
    {T₁ : R₁.ProgramTransformation MP MQ}
    {T₂ : R₂.ProgramTransformation MQ MS}
    {CP : ProgramResourceMeasure MP} {CQ : ProgramResourceMeasure MQ}
    {CS : ProgramResourceMeasure MS}
    (B₁ : T₁.ResourceBound CP CQ) (B₂ : T₂.ResourceBound CQ CS) :
    (T₁.comp T₂).ResourceBound CP CS where
  coefficient := B₂.coefficient * (B₁.coefficient + 1) ^ B₂.sourceDegree
  securityDegree := B₂.securityDegree + B₁.securityDegree * B₂.sourceDegree
  sourceDegree := B₁.sourceDegree * B₂.sourceDegree
  bound := by
    intro F prog n
    exact ResourcePolynomialBound.comp_le n _ _ _
      B₁.coefficient B₁.securityDegree B₁.sourceDegree
      B₂.coefficient B₂.securityDegree B₂.sourceDegree
      (B₁.bound F prog n)
      (B₂.bound (R₁.mapFamily F) (T₁.transform F prog) n)

/-- A polynomial source-program profile makes the explicit resource
majorant polynomially bounded. -/
theorem majorant_polynomiallyBounded
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    {T : R.ProgramTransformation MP MQ}
    {CP : ProgramResourceMeasure MP} {CQ : ProgramResourceMeasure MQ}
    (B : T.ResourceBound CP CQ)
    (F : InstanceFamily P) (prog : MP.Program F)
    (hSource : PolynomiallyBounded (CP.profile F prog)) :
    PolynomiallyBounded (fun n =>
      B.coefficient * (n + 1) ^ B.securityDegree *
        (CP.profile F prog n + 1) ^ B.sourceDegree) := by
  exact ResourcePolynomialBound.polynomiallyBounded hSource
    B.coefficient B.securityDegree B.sourceDegree

/-- The same transformed program both realizes the mapped adversary family
and has polynomially bounded target-program resource. -/
theorem preservesAdmissibility
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    {T : R.ProgramTransformation MP MQ}
    {CP : ProgramResourceMeasure MP} {CQ : ProgramResourceMeasure MQ}
    (B : T.ResourceBound CP CQ) :
    R.PreservesAdmissibility
      (MP.polynomialProgramClass CP) (MQ.polynomialProgramClass CQ) := by
  constructor
  intro F A hA
  rcases hA with ⟨prog, hRealize, hPoly⟩
  refine ⟨T.transform F prog, ?_, ?_⟩
  · calc
      MQ.realize (R.mapFamily F) (T.transform F prog) =
          R.mapAdversaryFamily F (MP.realize F prog) := T.realizes F prog
      _ = R.mapAdversaryFamily F A := by rw [hRealize]
  · exact PolynomiallyBounded.mono (B.bound F prog)
      (B.majorant_polynomiallyBounded F prog hPoly)

end ResourceBound

end Reduction.ProgramTransformation
