import Foundation.Crypto.Semantics.Resource.Reduction
import Foundation.Crypto.Semantics.Resource.Uniformity

universe u v w a b c

namespace Reduction

/-- A program-level realization of a reduction's adversary-family map.
For each source instance family, `transform` maps one source program to one
target program. The `realizes` equality says that realizing the transformed
program agrees with mapping the realized source family through the reduction.
This commuting condition does not assert an effective or efficient program
transformation. -/
structure ProgramTransformation {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (MP : UniformAdversaryModel.{u, a} P)
    (MQ : UniformAdversaryModel.{v, b} Q) where
  transform : ∀ (F : InstanceFamily P),
    MP.Program F → MQ.Program (R.mapFamily F)
  realizes : ∀ (F : InstanceFamily P) (prog : MP.Program F),
    MQ.realize (R.mapFamily F) (transform F prog) =
      R.mapAdversaryFamily F (MP.realize F prog)

namespace ProgramTransformation

/-- The identity reduction leaves the realizing program unchanged. -/
def id (P : CryptoGoal.{u}) (M : UniformAdversaryModel.{u, a} P) :
    (Reduction.id P).ProgramTransformation M M where
  transform := fun _ prog => prog
  realizes := by
    intro F prog
    rfl

/-- Compose program transformations in the same order as reductions:
`P → Q → S`. The three program universes remain independent. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    {R₁ : Reduction P Q} {R₂ : Reduction Q S}
    {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    {MS : UniformAdversaryModel.{w, c} S}
    (T₁ : R₁.ProgramTransformation MP MQ)
    (T₂ : R₂.ProgramTransformation MQ MS) :
    (R₁.comp R₂).ProgramTransformation MP MS where
  transform := fun F prog =>
    T₂.transform (R₁.mapFamily F) (T₁.transform F prog)
  realizes := by
    intro F prog
    change MS.realize (R₂.mapFamily (R₁.mapFamily F))
      (T₂.transform (R₁.mapFamily F) (T₁.transform F prog)) =
      R₂.mapAdversaryFamily (R₁.mapFamily F)
        (R₁.mapAdversaryFamily F (MP.realize F prog))
    rw [T₂.realizes (R₁.mapFamily F) (T₁.transform F prog),
      T₁.realizes F prog]

/-- Transforming a realizing program supplies a witness that the mapped
target adversary family is admitted by the target uniform class. -/
theorem preservesAdmissibility {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q} {MP : UniformAdversaryModel.{u, a} P}
    {MQ : UniformAdversaryModel.{v, b} Q}
    (T : R.ProgramTransformation MP MQ) :
    R.PreservesAdmissibility MP.uniformClass MQ.uniformClass := by
  constructor
  intro F A hA
  rcases hA with ⟨prog, rfl⟩
  exact ⟨T.transform F prog, T.realizes F prog⟩

end ProgramTransformation

end Reduction
