import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskPRG
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableInitializationEncoded

/-! Whole-prefix bit bounds for arbitrary finite native generators in the
block-mask experiment. The encoded generator is the actual supplied code. -/
namespace Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.Resources
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ReusableResponse.Initialized
open Foundation.Examples
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {width : Nat}
    (P : Machine.Procedure Input (Bits width)) (input : Input)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool)) (message : Bits width)
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

def initial : Control State := .initializing (.generating (P.execution.entry input))

def bitBound := Encoded.bound P.code FlaggedBlockXor.code ReusableBlockPad.code
  (Encoded.maxPc (ReusableBlockPad.callerFrame state trace message) (initial P input))
  (ReusableResponse.Initialized.Resources.extent stateSize (ReusableBlockPad.callerFrame state trace message)
    (initial P input)) (P.execution.budget input + 50 * width + 39) stateIncrement responseCap

include hState hOracle in
theorem peak (elapsed : Nat) (hElapsed : elapsed ≤ P.execution.budget input + 50 * width + 39)
    (target : Control State)
    (hTarget : target ∈ (TimedExecution.eval (GeneratedBlockMask.step P oracle state trace message) elapsed
      (initial P input)).support) :
    ((Encoded.completeEncoding E).encode
      (P.code, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (ReusableBlockPad.callerFrame state trace message, target))).length ≤
      bitBound P input state trace message stateSize stateIncrement responseCap :=
  Encoded.encoded_peak E stateSize hState P.code FlaggedBlockXor.code ReusableBlockPad.code oracle
    (ReusableBlockPad.callerFrame state trace message) stateIncrement responseCap hOracle
    (P.execution.budget input + 50 * width + 39) elapsed hElapsed (initial P input) target hTarget

/-- Code remains fixed across the profiles. Generation time, message width,
initial tapes and external transitions must have proved polynomial bounds. -/
theorem bound_polynomial (generator : Program)
    {generation width initialPc initialExtent increments responses : Nat → Nat}
    (hGeneration : PolynomiallyBounded generation) (hWidth : PolynomiallyBounded width)
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hIncrement : PolynomiallyBounded increments) (hResponse : PolynomiallyBounded responses) :
    PolynomiallyBounded (fun n => Encoded.bound generator FlaggedBlockXor.code ReusableBlockPad.code
      (initialPc n) (initialExtent n) (generation n + 50 * width n + 39) (increments n) (responses n)) :=
  Encoded.bound_polynomial generator FlaggedBlockXor.code ReusableBlockPad.code hPc hExtent
    (GeneratedBlockMask.budget_polynomial hGeneration hWidth) hIncrement hResponse

end Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.Resources
