import Foundation.Crypto.Semantics.Resource.Uniformity

universe u v

namespace UniformAdversaryModel

/-- A finite bitstring description of every program object, relative to a
fixed instance family `F`. Injectivity makes the description identify the
program uniquely. This does not encode `F`, provide a decoder, or assert
effective computation or execution of the code. -/
structure FiniteDescription {P : CryptoGoal.{u}}
    (M : UniformAdversaryModel.{u, v} P) where
  encode : ∀ (F : InstanceFamily P), M.Program F → List Bool
  encode_injective : ∀ (F : InstanceFamily P), Function.Injective (encode F)

end UniformAdversaryModel
