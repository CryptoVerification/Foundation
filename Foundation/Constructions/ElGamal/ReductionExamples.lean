import Foundation.Constructions.ElGamal.ToDDH
import Foundation.Constructions.ElGamal.Examples

namespace Foundation.Constructions.ElGamal.ReductionExamples

open Foundation.Notions.PKE.Examples (Plain)
open Foundation.Constructions.ElGamal.Examples (dummyInstance)

/-- The second stage observes both ciphertext components, so this checks the
challenge builder as well as the sequencing of the two stages. -/
def observingAdversary : INDCPAAdversary Plain dummyInstance.scheme where
  State := Bool
  choose := fun publicKey => (false, true, publicKey)
  guess := fun state ciphertext => state && ciphertext.1 && ciphertext.2

def dummyDistinguisher : DDHAdversary Plain dummyInstance.params :=
  ddhAdversaryOfINDCPA (M := Id) (pure true) dummyInstance observingAdversary

example (X Y T : dummyInstance.params.Element) :
    Plain Bool :=
  dummyDistinguisher.distinguish X Y T

example (X Y T : Bool) :
    dummyDistinguisher.distinguish X Y T = (X && Y && T) := by
  cases X <;> cases Y <;> cases T <;> rfl

end Foundation.Constructions.ElGamal.ReductionExamples
