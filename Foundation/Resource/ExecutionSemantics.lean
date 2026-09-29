import Foundation.Resource.Uniformity

universe u v

namespace UniformAdversaryModel

/-- An explicit execution function for one program across all security
parameters, compatible with the model's adversary-family realization.
This semantic interface alone does not assert that execution is computable
or that a finite code can be interpreted. -/
structure ExecutionSemantics {P : CryptoGoal.{u}}
    (M : UniformAdversaryModel.{u, v} P) where
  execute : ∀ (F : InstanceFamily P) (_prog : M.Program F) (n : Nat),
    P.Adversary n (F n)
  realizes : ∀ (F : InstanceFamily P) (prog : M.Program F),
    (fun n => execute F prog n) = M.realize F prog

end UniformAdversaryModel
