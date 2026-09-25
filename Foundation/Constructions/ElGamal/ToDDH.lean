import Foundation.Assumptions.DDH.DDH
import Foundation.Constructions.ElGamal.Basic
import Foundation.Notions.PKE.INDCPA

/-- Simulate an ElGamal IND-CPA challenge from a DDH challenge.

`chooseBit` supplies the reduction's challenge bit. The output reports whether
the IND-CPA guess matches that bit. The distinguisher never inspects the DDH
challenge's real/random origin. This construction asserts no advantage relation
and assumes no correctness law for `I.construction`. -/
def ddhAdversaryOfINDCPA {M : Type → Type} [Monad M]
    (chooseBit : M Bool) (I : ElGamalInstance M)
    (A : INDCPAAdversary M I.scheme) : DDHAdversary M I.params where
  distinguish := fun X Y T => do
    let (m₀, m₁, state) ← A.choose X
    let β ← chooseBit
    let message := if β then m₁ else m₀
    let guess ← A.guess state (ElGamal.challengeCiphertext I.params message Y T)
    pure (guess == β)
