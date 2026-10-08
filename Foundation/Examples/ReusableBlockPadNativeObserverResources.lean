import Foundation.Examples.ReusableBlockPadNativeObserver
import Foundation.Examples.ReusableBlockPadResources
import Foundation.Examples.ReusableBlockPadEncodedBackend
import Foundation.Crypto.Semantics.Machine.NativeContinuationResources

/-! Faithful whole-prefix storage for the arbitrary-width pad and native
observer together. Counts all five finite codes, the original caller, private
key/history, every producer phase, and the native observer's physical state. -/
namespace Foundation.Examples.ReusableBlockPad.NativeObserver.Resources
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

/-- Retain the original caller and complete producer state. Fixed source
codes are encoded once outside the phase state, avoiding repeated code copies. -/
def sourceEncoding : FiniteBitEncoding (RuntimeState State) :=
  (Encoded.encoding E).retract (fun target => (callerFrame state trace message, target))
    Prod.snd (fun _ => rfl)

theorem source_encode (target : RuntimeState State) :
    (sourceEncoding state trace message E).encode target =
      (Encoded.encoding E).encode (callerFrame state trace message, target) := rfl

def completeEncoding :=
  NativeContinuation.Resources.programEncoding.prod
    (NativeContinuation.Resources.programEncoding.prod
      (NativeContinuation.Resources.programEncoding.prod
        (EncodedStorage.codeEncoding.prod
          (NativeContinuation.Resources.completeEncoding (sourceEncoding state trace message E)))))

theorem codes_length (generator copy handler : Program) (callerCode : Code)
    (observer : Program) (target : NativeContinuation.Control (RuntimeState State)) :
    ((completeEncoding state trace message E).encode
      (generator, copy, handler, callerCode, (observer, target))).length =
      Encoded.codeBits generator copy handler callerCode +
        ((NativeContinuation.Resources.completeEncoding (sourceEncoding state trace message E)).encode
          (observer, target)).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length,
    NativeContinuation.Resources.programEncoding, Encoded.codeBits, ReusableResponse.Encoded.codeBits]
  omega

def sourceCodeBits := Encoded.codeBits Machine.OneTimePad.keygen PrivateKeyCopy.code
  FlaggedBlockXor.code ReusableBlockPad.code

theorem complete_length (observer : Program) (target : NativeContinuation.Control (RuntimeState State)) :
    ((completeEncoding state trace message E).encode
      (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (observer, target))).length = sourceCodeBits +
      ((NativeContinuation.Resources.completeEncoding (sourceEncoding state trace message E)).encode
        (observer, target)).length :=
  codes_length state trace message E _ _ _ _ observer target

def horizon (width observerCap : Nat) := 55 * width + 42 + observerCap

def sourceBound (observerCap : Nat) :=
  Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    (Encoded.maxPc (callerFrame state trace message) (ReusableBlockPad.Resources.initial (State := State) (width := width)))
    (ReusableResponse.Initialized.Resources.extent stateSize (callerFrame state trace message)
      (ReusableBlockPad.Resources.initial (State := State) (width := width)))
    (horizon width observerCap) stateIncrement responseCap

def publicTapeBound (observerCap : Nat) :=
  ReusableInitializationStorage.bound
    (ReusableResponse.Initialized.Resources.extent stateSize (callerFrame state trace message)
      (ReusableBlockPad.Resources.initial (State := State) (width := width)))
    (horizon width observerCap) (stateIncrement + responseCap + 4) 3 0 + 2

def bitBound (observer : Program) (observerCap : Nat) :=
  sourceCodeBits + NativeContinuation.Resources.bound observer
    (sourceBound state trace message stateSize stateIncrement responseCap observerCap)
    (publicTapeBound state trace message stateSize stateIncrement responseCap observerCap)
    (horizon width observerCap)

/-- The public machine is a measured part of the real producer state.
Non-public phases use the empty default machine, contributing two cells. -/
theorem public_cells (target : RuntimeState State) :
    (publicMachine target).tapeCells ≤
      ReusableResponse.Initialized.Resources.cells stateSize (callerFrame state trace message) target + 2 := by
  cases target with
  | initializing component =>
      simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.Configuration.tapeCells, Machine.Tape.cells,
        ReusableResponse.Initialized.Resources.cells, ReusableInitializationStorage.cells]
  | aligning tape =>
      simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.Configuration.tapeCells, Machine.Tape.cells,
        ReusableResponse.Initialized.Resources.cells, ReusableInitializationStorage.cells]
  | active source =>
      cases source with
      | processing =>
          simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.Configuration.tapeCells, Machine.Tape.cells,
            ReusableResponse.Initialized.Resources.cells, ReusableInitializationStorage.cells]
      | calling =>
          simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.Configuration.tapeCells, Machine.Tape.cells,
            ReusableResponse.Initialized.Resources.cells, ReusableInitializationStorage.cells]
      | source retained frame =>
          rcases frame with ⟨saved, control, history⟩
          cases control <;> simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.Configuration.tapeCells, Machine.Tape.cells,
            ReusableResponse.Initialized.Resources.cells, ReusableInitializationStorage.cells,
            ReusableInitializationStorage.phaseCells, ReusableResponseStorage.cells,
            SourceStorage.cells, SourceStorage.controlCells] <;> omega

include hState hOracle in
/-- Bounds every supported execution prefix, also while the native observer
is running. Observer halting and security assumptions are unnecessary here. -/
theorem peak (observer : Program) (observerCap elapsed : Nat)
    (hElapsed : elapsed ≤ horizon width observerCap)
    (target : NativeContinuation.Control (RuntimeState State))
    (hTarget : target ∈ (TimedExecution.eval
      (NativeContinuation.step (ReusableBlockPad.step oracle state trace message)
        boundary publicMachine observer) elapsed
      (.producing (ReusableBlockPad.Resources.initial (State := State) (width := width)))).support) :
    ((completeEncoding state trace message E).encode
      (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (observer, target))).length ≤
      bitBound state trace message stateSize stateIncrement responseCap observer observerCap := by
  rw [complete_length]
  apply Nat.add_le_add_left
  apply NativeContinuation.Resources.encoded_peak
    (ReusableBlockPad.step oracle state trace message) boundary publicMachine observer
    (sourceEncoding state trace message E)
    (ReusableBlockPad.Resources.initial (State := State) (width := width))
    (sourceBound state trace message stateSize stateIncrement responseCap observerCap)
    (publicTapeBound state trace message stateSize stateIncrement responseCap observerCap)
    (horizon width observerCap) _ _ elapsed hElapsed target hTarget
  · intro elapsed he target ht
    rw [source_encode]
    have hb := Encoded.encoded_peak E stateSize hState Machine.OneTimePad.keygen FlaggedBlockXor.code
      ReusableBlockPad.code oracle (callerFrame state trace message) stateIncrement responseCap hOracle
      (horizon width observerCap) elapsed he
      (ReusableBlockPad.Resources.initial (State := State) (width := width)) target ht
    rw [Encoded.complete_length] at hb
    exact (Nat.le_add_left _ _).trans hb
  · intro elapsed he target ht _
    have hc := ReusableResponse.Initialized.Resources.peak stateSize (callerFrame state trace message)
      Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code oracle stateIncrement responseCap hOracle
      (horizon width observerCap) elapsed he
      (ReusableBlockPad.Resources.initial (State := State) (width := width)) target ht
    have hp := public_cells state trace message stateSize target
    exact hp.trans (Nat.add_le_add_right hc 2)

/-- Separate public profiles may bound addresses, initial retained data,
external replies and observer time. All five finite codes stay fixed. -/
theorem bound_polynomial (observer : Program)
    {width observerCap initialPc initialExtent increments responses : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hObserver : PolynomiallyBounded observerCap)
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hIncrement : PolynomiallyBounded increments) (hResponse : PolynomiallyBounded responses) :
    PolynomiallyBounded (fun n => sourceCodeBits + NativeContinuation.Resources.bound observer
      (Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
        (initialPc n) (initialExtent n) (horizon (width n) (observerCap n)) (increments n) (responses n))
      (ReusableInitializationStorage.bound (initialExtent n) (horizon (width n) (observerCap n))
        (increments n + responses n + 4) 3 0 + 2)
      (horizon (width n) (observerCap n))) := by
  have hTime := NativeObserver.time_polynomial hWidth hObserver
  have hSource := Encoded.bound_polynomial Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    hPc hExtent hTime hIncrement hResponse
  have hPublic := (ReusableInitializationStorage.bound_polynomial hExtent hTime
    ((hIncrement.add hResponse).add (PolynomiallyBounded.const 4)) 3 0).add (PolynomiallyBounded.const 2)
  exact (PolynomiallyBounded.const sourceCodeBits).add
    (NativeContinuation.Resources.bound_polynomial observer hSource hPublic hTime)

/-- A concrete cap when no external oracle data is retained. -/
def unitBound (observer : Program) (width observerCap : Nat) :=
  sourceCodeBits + NativeContinuation.Resources.bound observer
    (Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
      0 (2 * width + 3) (horizon width observerCap) 0 0)
    (ReusableInitializationStorage.bound (2 * width + 3) (horizon width observerCap) 4 3 0 + 2)
    (horizon width observerCap)

private theorem public_bound_mono {first next : Nat} (h : first ≤ next) (horizon : Nat) :
    ReusableInitializationStorage.bound first horizon 4 3 0 + 2 ≤
      ReusableInitializationStorage.bound next horizon 4 3 0 + 2 := by
  have he := Nat.add_le_add_right h (horizon * (4 + 1))
  have hq := Nat.pow_le_pow_left he 2
  simp only [ReusableInitializationStorage.bound]
  omega

/-- All external-state, reply-size and initial-layout conditions are
proved for this instance, rather than supplied as assumptions. -/
theorem unit_peak (message : Bits width) (observer : Program) (observerCap elapsed : Nat)
    (hElapsed : elapsed ≤ horizon width observerCap)
    (target : NativeContinuation.Control (RuntimeState Unit))
    (hTarget : target ∈ (TimedExecution.eval
      (NativeContinuation.step
        (ReusableBlockPad.step ReusableBlockPadEncodedBackend.unitOracle () [] message)
        boundary publicMachine observer) elapsed
      (.producing (ReusableBlockPad.Resources.initial (State := Unit) (width := width)))).support) :
    ((completeEncoding () [] message FiniteBitEncoding.unit).encode
      (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (observer, target))).length ≤ unitBound observer width observerCap := by
  have hp := peak ReusableBlockPadEncodedBackend.unitOracle () [] message FiniteBitEncoding.unit
    (fun _ => 0) (fun _ => Nat.le_refl 0) 0 0
    (by
      intro saved request result hr
      rw [ReusableBlockPadEncodedBackend.unitOracle, PMF.mem_support_pure_iff] at hr
      subst result
      simp)
    observer observerCap elapsed hElapsed target hTarget
  let c : ReusableBlockPadBackend.Context Unit :=
    ⟨ReusableBlockPadEncodedBackend.unitOracle, (), [], width, message, fun _ => false⟩
  have he := ReusableBlockPadEncodedBackend.initial_extent (fun _ : Unit => 0) c
  change ReusableResponse.Initialized.Resources.extent (fun _ => 0)
    (callerFrame () [] message) (ReusableBlockPad.Resources.initial (State := Unit) (width := width)) ≤
      2 * width + 0 + ControllerExtent.traceExtent [] + 3 at he
  simp only [ControllerExtent.traceExtent, Nat.add_zero] at he
  have hs := Encoded.bound_mono_initial Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    (firstPc := 0) (nextPc := 0) (Nat.le_refl _) he (horizon width observerCap) 0 0
  have ht := public_bound_mono he (horizon width observerCap)
  have hb := NativeContinuation.Resources.bound_mono observer hs ht (horizon width observerCap)
  exact hp.trans (Nat.add_le_add_left hb sourceCodeBits)

theorem unitBound_polynomial (observer : Program) {width observerCap : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (fun n => unitBound observer (width n) (observerCap n)) :=
  bound_polynomial observer hWidth hObserver (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 3))
    (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 0)

end Foundation.Examples.ReusableBlockPad.NativeObserver.Resources
