import Foundation.Resource.FiniteProgram
import Foundation.Resource.ExecutionCost

universe u v w

namespace UniformAdversaryModel

/-- Families realized by one finitely describable program whose validated
execution trace has polynomially bounded length. The finite-description
witness is model-level; the realizing program and runtime witness coincide.
This is not named PPT because the abstract step relation does not yet
interpret finite codes as a concrete effective machine. -/
def polynomialExecutionClass {P : CryptoGoal.{u}}
    (M : UniformAdversaryModel.{u, v} P)
    (_D : M.FiniteDescription)
    {E : M.ExecutionSemantics} (C : E.ExecutionCost.{u, v, w}) :
    AdversaryClass P :=
  M.polynomialProgramClass C.toProgramResourceMeasure

end UniformAdversaryModel
