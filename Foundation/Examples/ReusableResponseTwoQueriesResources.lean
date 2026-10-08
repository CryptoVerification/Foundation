import Foundation.Examples.ReusableResponseTwoQueries
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseEncoded

/-! Every actual prefix of the two-query witness has a complete finite-code
and runtime bit bound. Arbitrary initial keys, requests, states and histories
are counted, including intermediate copying and response delivery. -/
namespace Foundation.Examples.ReusableResponseTwoQueries
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
universe u

variable {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (key : List Bool) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

def initial : ReusableResponse.Control State :=
  .source (ResponseHandoffProgram.retainedKey key) ⟨state, .running (caller request), trace⟩

def bitBound :=
  ReusableResponse.Encoded.bound native code
    (ReusableResponse.Encoded.maxPc (initial key state trace request))
    (ReusableResponse.Resources.extent stateSize (initial key state trace request))
    (18 * key.length + 5 * request.length + 66) stateIncrement responseCap

include hState hOracle in
theorem encoded_prefix (elapsed : Nat)
    (hElapsed : elapsed ≤ 18 * key.length + 5 * request.length + 66)
    (target : ReusableResponse.Control State)
    (hTarget : target ∈ (TimedExecution.eval (ReusableResponse.step native code oracle)
      elapsed (initial key state trace request)).support) :
    ((ReusableResponse.Encoded.completeEncoding E).encode
      (PrivateKeyCopy.code, native, code, target)).length ≤
      bitBound stateSize key state trace request stateIncrement responseCap :=
  ReusableResponse.Encoded.encoded_peak E stateSize hState native code oracle
    stateIncrement responseCap hOracle _ elapsed hElapsed _ target hTarget

end Foundation.Examples.ReusableResponseTwoQueries
