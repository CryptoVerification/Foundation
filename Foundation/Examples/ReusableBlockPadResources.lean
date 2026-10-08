import Foundation.Examples.ReusableBlockPad
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableInitializationEncoded

/-! Whole-prefix bit bounds for the real arbitrary-width pad experiment,
including key generation, all four finite codes and the original caller. -/
namespace Foundation.Examples.ReusableBlockPad.Resources
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open ReusableResponse.Initialized
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) {width : Nat} (message : Bits width)
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

def initial : Control State :=
  .initializing (.generating (Machine.Configuration.initial (List.replicate width true)))

def bitBound := Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
  (Encoded.maxPc (callerFrame state trace message) (initial (State := State) (width := width)))
  (ReusableResponse.Initialized.Resources.extent stateSize (callerFrame state trace message)
    (initial (State := State) (width := width)))
  (55 * width + 41) stateIncrement responseCap

include hState hOracle in
/-- Every actual intermediate state is covered, including native generation
and request handling, not merely the final ciphertext tape. -/
theorem peak (elapsed : Nat) (hElapsed : elapsed ≤ 55 * width + 41) (target : Control State)
    (hTarget : target ∈ (TimedExecution.eval (ReusableBlockPad.step oracle state trace message) elapsed
      (initial (State := State) (width := width))).support) :
    ((Encoded.completeEncoding E).encode
      (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (callerFrame state trace message, target))).length ≤
      bitBound state trace message stateSize stateIncrement responseCap :=
  Encoded.encoded_peak E stateSize hState Machine.OneTimePad.keygen FlaggedBlockXor.code
    ReusableBlockPad.code oracle (callerFrame state trace message) stateIncrement responseCap hOracle
    (55 * width + 41) elapsed hElapsed (initial (State := State) (width := width)) target hTarget

/-- Public profiles can bound initial state and address size independently
of the typed message representation and external-state encoding. -/
theorem bound_polynomial {width initialPc initialExtent increments responses : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hPc : PolynomiallyBounded initialPc)
    (hExtent : PolynomiallyBounded initialExtent) (hIncrement : PolynomiallyBounded increments)
    (hResponse : PolynomiallyBounded responses) :
    PolynomiallyBounded (fun n => Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
      (initialPc n) (initialExtent n) (55 * width n + 41) (increments n) (responses n)) :=
  Encoded.bound_polynomial Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    hPc hExtent (ReusableBlockPad.time_polynomial hWidth) hIncrement hResponse

end Foundation.Examples.ReusableBlockPad.Resources
