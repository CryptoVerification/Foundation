import Foundation.Notions.PKE.Basic
import Foundation.Probability.Comp

open Foundation.Probability

namespace PKE

/-- Perfect decryption correctness: every supported key pair and every
supported encryption of a message decrypts to that message. This property
is separate from the scheme syntax and from IND-CPA security. -/
def Correct (S : PKE ProbComp) : Prop :=
  ∀ m pk sk ct,
    (pk, sk) ∈ S.keygen.support →
    ct ∈ (S.encrypt pk m).support →
    S.decrypt sk ct = some m

end PKE
