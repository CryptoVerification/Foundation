import Foundation.Assumptions.DDH.Basic
import Foundation.Notions.PKE.Basic

namespace ElGamal

/-- Form the simulated ciphertext from a message and the last two DDH elements. -/
def challengeCiphertext (params : DDHParameters)
    (message Y T : params.Element) : params.Element × params.Element :=
  (Y, params.mul message T)

end ElGamal

/-- Operations with the type shape of ElGamal over fixed DDH parameters.

The operations are abstract: this interface does not assert the ElGamal
arithmetic, randomness, or correctness laws. -/
structure ElGamalConstruction (M : Type → Type) (params : DDHParameters) where
  keygen : M (params.Element × params.Scalar)
  encrypt : params.Element → params.Element →
    M (params.Element × params.Element)
  decrypt : params.Scalar → (params.Element × params.Element) →
    Option params.Element

namespace ElGamalConstruction

/-- Interpret the parameter-indexed construction as a PKE scheme. -/
def scheme {M : Type → Type} {params : DDHParameters}
    (C : ElGamalConstruction M params) : PKE M where
  PublicKey := params.Element
  SecretKey := params.Scalar
  Message := params.Element
  Ciphertext := params.Element × params.Element
  keygen := C.keygen
  encrypt := C.encrypt
  decrypt := C.decrypt

end ElGamalConstruction

/-- Keep the construction and its underlying DDH parameters together. -/
structure ElGamalInstance (M : Type → Type) where
  params : DDHParameters
  construction : ElGamalConstruction M params

namespace ElGamalInstance

def scheme {M : Type → Type} (I : ElGamalInstance M) : PKE M :=
  I.construction.scheme

end ElGamalInstance
