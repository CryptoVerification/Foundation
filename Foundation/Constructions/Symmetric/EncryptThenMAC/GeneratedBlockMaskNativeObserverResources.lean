import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskNativeObserver
import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskResources
import Foundation.Examples.ReusableBlockPadNativeObserverResources

/-! Whole-prefix encoded memory for arbitrary finite generators followed by
block masking and a finite native observer. Reuses the same phase codec and
public-tape inclusion proof as the uniform-pad instance. -/
namespace Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.NativeObserver.Resources
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ReusableResponse.Initialized
open Foundation.Examples
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine)
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

def sourceEncoding := ReusableBlockPad.NativeObserver.Resources.sourceEncoding state trace message E
def completeEncoding := ReusableBlockPad.NativeObserver.Resources.completeEncoding state trace message E

def sourceCodeBits (generator : Program) :=
  Encoded.codeBits generator PrivateKeyCopy.code FlaggedBlockXor.code ReusableBlockPad.code

theorem complete_length (observer : Program) (target : NativeContinuation.Control (RuntimeState State)) :
    ((completeEncoding state trace message E).encode
      (P.code, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code, (observer, target))).length =
      sourceCodeBits P.code +
        ((NativeContinuation.Resources.completeEncoding (sourceEncoding state trace message E)).encode
          (observer, target)).length :=
  ReusableBlockPad.NativeObserver.Resources.codes_length state trace message E _ _ _ _ observer target

def horizon (generation width observerCap : Nat) := generation + 50 * width + 40 + observerCap

def sourceBound (observerCap : Nat) :=
  Encoded.bound P.code FlaggedBlockXor.code ReusableBlockPad.code
    (Encoded.maxPc (ReusableBlockPad.callerFrame state trace message) (GeneratedBlockMask.Resources.initial P input))
    (ReusableResponse.Initialized.Resources.extent stateSize (ReusableBlockPad.callerFrame state trace message)
      (GeneratedBlockMask.Resources.initial P input))
    (horizon (P.execution.budget input) width observerCap) stateIncrement responseCap

def publicTapeBound (observerCap : Nat) :=
  ReusableInitializationStorage.bound
    (ReusableResponse.Initialized.Resources.extent stateSize (ReusableBlockPad.callerFrame state trace message)
      (GeneratedBlockMask.Resources.initial P input))
    (horizon (P.execution.budget input) width observerCap) (stateIncrement + responseCap + 4) 3 0 + 2

def bitBound (observer : Program) (observerCap : Nat) :=
  sourceCodeBits P.code + NativeContinuation.Resources.bound observer
    (sourceBound P input state trace message stateSize stateIncrement responseCap observerCap)
    (publicTapeBound P input state trace message stateSize stateIncrement responseCap observerCap)
    (horizon (P.execution.budget input) width observerCap)

include hState hOracle in
/-- Covers the actual supplied generator and observer codes and every
supported intermediate state. No PRG, halt or security premise is required. -/
theorem peak (observer : Program) (observerCap elapsed : Nat)
    (hElapsed : elapsed ≤ horizon (P.execution.budget input) width observerCap)
    (target : NativeContinuation.Control (RuntimeState State))
    (hTarget : target ∈ (TimedExecution.eval
      (NativeContinuation.step (GeneratedBlockMask.step P oracle state trace message)
        boundary publicMachine observer) elapsed
      (.producing (GeneratedBlockMask.Resources.initial P input))).support) :
    ((completeEncoding state trace message E).encode
      (P.code, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (observer, target))).length ≤
      bitBound P input state trace message stateSize stateIncrement responseCap observer observerCap := by
  rw [complete_length]
  apply Nat.add_le_add_left
  apply NativeContinuation.Resources.encoded_peak
    (GeneratedBlockMask.step P oracle state trace message) boundary publicMachine observer
    (sourceEncoding state trace message E) (GeneratedBlockMask.Resources.initial P input)
    (sourceBound P input state trace message stateSize stateIncrement responseCap observerCap)
    (publicTapeBound P input state trace message stateSize stateIncrement responseCap observerCap)
    (horizon (P.execution.budget input) width observerCap) _ _ elapsed hElapsed target hTarget
  · intro elapsed he target ht
    rw [sourceEncoding, ReusableBlockPad.NativeObserver.Resources.source_encode]
    have hb := Encoded.encoded_peak E stateSize hState P.code FlaggedBlockXor.code ReusableBlockPad.code oracle
      (ReusableBlockPad.callerFrame state trace message) stateIncrement responseCap hOracle
      (horizon (P.execution.budget input) width observerCap) elapsed he
      (GeneratedBlockMask.Resources.initial P input) target ht
    rw [Encoded.complete_length] at hb
    exact (Nat.le_add_left _ _).trans hb
  · intro elapsed he target ht _
    have hc := ReusableResponse.Initialized.Resources.peak stateSize (ReusableBlockPad.callerFrame state trace message)
      P.code FlaggedBlockXor.code ReusableBlockPad.code oracle stateIncrement responseCap hOracle
      (horizon (P.execution.budget input) width observerCap) elapsed he
      (GeneratedBlockMask.Resources.initial P input) target ht
    have hp := ReusableBlockPad.NativeObserver.Resources.public_cells state trace message stateSize target
    exact hp.trans (Nat.add_le_add_right hc 2)

/-- Both native programs stay fixed throughout these public profiles. -/
theorem bound_polynomial (generator observer : Program)
    {generation width observerCap initialPc initialExtent increments responses : Nat → Nat}
    (hGeneration : PolynomiallyBounded generation) (hWidth : PolynomiallyBounded width)
    (hObserver : PolynomiallyBounded observerCap)
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hIncrement : PolynomiallyBounded increments) (hResponse : PolynomiallyBounded responses) :
    PolynomiallyBounded (fun n => sourceCodeBits generator + NativeContinuation.Resources.bound observer
      (Encoded.bound generator FlaggedBlockXor.code ReusableBlockPad.code
        (initialPc n) (initialExtent n) (horizon (generation n) (width n) (observerCap n)) (increments n) (responses n))
      (ReusableInitializationStorage.bound (initialExtent n) (horizon (generation n) (width n) (observerCap n))
        (increments n + responses n + 4) 3 0 + 2)
      (horizon (generation n) (width n) (observerCap n))) := by
  have hTime := GeneratedBlockMask.NativeObserver.time_polynomial hGeneration hWidth hObserver
  have hSource := Encoded.bound_polynomial generator FlaggedBlockXor.code ReusableBlockPad.code
    hPc hExtent hTime hIncrement hResponse
  have hPublic := (ReusableInitializationStorage.bound_polynomial hExtent hTime
    ((hIncrement.add hResponse).add (PolynomiallyBounded.const 4)) 3 0).add (PolynomiallyBounded.const 2)
  exact (PolynomiallyBounded.const (sourceCodeBits generator)).add
    (NativeContinuation.Resources.bound_polynomial observer hSource hPublic hTime)

end Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.NativeObserver.Resources
