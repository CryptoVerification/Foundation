import Foundation.Crypto.Semantics.Resource.ProgramMeasure
import Foundation.Crypto.Semantics.Resource.UniformReduction

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
    let s := CP.profile F prog n
    let t := CQ.profile (R₁.mapFamily F) (T₁.transform F prog) n
    let u := CS.profile ((R₁.comp R₂).mapFamily F)
      ((T₁.comp T₂).transform F prog) n
    let X := (n + 1) ^ B₁.securityDegree * (s + 1) ^ B₁.sourceDegree
    have ht : t ≤ B₁.coefficient * X := by
      simpa only [t, X, s, mul_assoc] using B₁.bound F prog n
    have hX : 1 ≤ X := by
      dsimp [X, s]
      calc
        1 = 1 * 1 := by simp
        _ ≤ (n + 1) ^ B₁.securityDegree *
            (CP.profile F prog n + 1) ^ B₁.sourceDegree :=
          Nat.mul_le_mul
            (Nat.one_le_pow' B₁.securityDegree n)
            (Nat.one_le_pow' B₁.sourceDegree (CP.profile F prog n))
    have htPlus : t + 1 ≤ (B₁.coefficient + 1) * X := by
      calc
        t + 1 ≤ B₁.coefficient * X + 1 := Nat.add_le_add_right ht 1
        _ ≤ B₁.coefficient * X + X := Nat.add_le_add_left hX _
        _ = (B₁.coefficient + 1) * X := by simp [Nat.add_mul]
    have hu : u ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
        (t + 1) ^ B₂.sourceDegree := by
      change CS.profile (R₂.mapFamily (R₁.mapFamily F))
        (T₂.transform (R₁.mapFamily F) (T₁.transform F prog)) n ≤
          B₂.coefficient * (n + 1) ^ B₂.securityDegree *
            (CQ.profile (R₁.mapFamily F) (T₁.transform F prog) n + 1) ^
              B₂.sourceDegree
      exact B₂.bound (R₁.mapFamily F) (T₁.transform F prog) n
    calc
      u ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
          (t + 1) ^ B₂.sourceDegree := hu
      _ ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
          ((B₁.coefficient + 1) * X) ^ B₂.sourceDegree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htPlus _)
      _ = (B₂.coefficient * (B₁.coefficient + 1) ^ B₂.sourceDegree) *
          (n + 1) ^ (B₂.securityDegree + B₁.securityDegree * B₂.sourceDegree) *
          (CP.profile F prog n + 1) ^ (B₁.sourceDegree * B₂.sourceDegree) := by
        dsimp [X, s]
        simp only [mul_pow, pow_mul, pow_add]
        ac_rfl

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
  have hSourcePlusOne : PolynomiallyBounded
      (fun n => CP.profile F prog n + 1) :=
    PolynomiallyBounded.add hSource (PolynomiallyBounded.const 1)
  have hSourcePower : PolynomiallyBounded
      (fun n => (CP.profile F prog n + 1) ^ B.sourceDegree) :=
    PolynomiallyBounded.pow hSourcePlusOne B.sourceDegree
  have hParameterPlusOne : PolynomiallyBounded (fun n => n + 1) :=
    PolynomiallyBounded.add PolynomiallyBounded.id
      (PolynomiallyBounded.const 1)
  have hParameterPower : PolynomiallyBounded
      (fun n => (n + 1) ^ B.securityDegree) :=
    PolynomiallyBounded.pow hParameterPlusOne B.securityDegree
  exact PolynomiallyBounded.mul
    (PolynomiallyBounded.mul
      (PolynomiallyBounded.const B.coefficient) hParameterPower)
    hSourcePower

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
