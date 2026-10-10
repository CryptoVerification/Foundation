import Foundation.Constructions.Hash.NativeAdaptivePublicHalt
import Foundation.Constructions.Hash.NativePublicWorldResources

/-! Complete encoded storage along the concrete adaptive two-query caller,
including its genuine first-halt endpoint. Time counts machine transitions
with atomic ideal compression; encoded bits are not physical RAM usage. -/
namespace Foundation.Hash.Native.AdaptivePublicCaller
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

variable {n κ : Nat} (marker : Bool) (payload : Bits κ) {State : Type*}
    (ES : FiniteBitEncoding State) (stateSize : State → Nat)
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (state : State) (trace : List (List Bool × List Bool)) (input : Tape) (message : List (Bits κ))
    (saved : Configuration (IdealTable n κ)) (stateIncrement responseCap : Nat)

def transitionBound (n κ count : Nat) : Nat := count * (7 * n + 27 * κ + 33) + 32 * n + 15 * κ + 103

/-- Count fixed code and fixed environment even while only the caller runs.
The complete actual entry, including all retained cells and table entries,
determines the starting size. -/
def encodedBound : Nat :=
  2 * (EncodedStorage.codeEncoding.encode (runtimeLinkedHashCode initial.toList terminal.toList)).length +
    2 * (EncodedStorage.codeEncoding.encode NativeCompressionCall.code).length +
    2 * (ConfigurationEncoding.trace.encode prior).length + 6 +
    PacketResponseEncoding.bitBoundWith (code n marker payload) [] nativeWorldComponentBound runtimeRawSavedBound
      (PacketResponseGrowth.size (nativeWorldSize (n := n) (κ := κ) prior) stateSize (runtimeRawSavedSize prior)
        (.source saved ⟨state, .running (firstMachine (n := n) input message), trace⟩))
      (transitionBound n κ message.length)
      (PacketResponseGrowth.increment (code n marker payload) (nativeWorldIncrement initial terminal) 0 0
        stateIncrement responseCap)

variable (oracle : BitOracle State)
    (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hState hOracle in
/-- Every supported physical intermediate state, not only call boundaries,
is bounded through the whole caller's concrete transition horizon. -/
theorem whole_encoded_peak
    (target : PacketResponseSource.Control (NativeWorldComponent n κ) State (Configuration (IdealTable n κ)))
    (elapsed : Nat) (within : elapsed ≤ transitionBound n κ message.length)
    (support : target ∈ (TimedExecution.eval (nativeWorldCallerStep initial terminal prior (code n marker payload) oracle)
      elapsed (.source saved ⟨state, .running (firstMachine (n := n) input message), trace⟩)).support) :
    ((nativeWorldCallerEncoding (n := n) (κ := κ) ES).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, NativeCompressionCall.code, false, prior,
        code n marker payload, [], target)).length ≤
    encodedBound marker payload stateSize initial terminal prior state trace input message saved stateIncrement responseCap :=
  nativeWorldCaller_encoded_peak ES stateSize hState initial terminal prior (code n marker payload) oracle
    stateIncrement responseCap hOracle _ _ _ elapsed within support

include hState hOracle in
/-- Specialize the same peak bound to the actual first whole-caller halt,
without replacing its physical final frame by a canonical smaller state. -/
theorem firstHalt_encoded_endpoint
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (result : PacketResponseSource.Control (NativeWorldComponent n κ) State (Configuration (IdealTable n κ)) × Nat)
    (support : result ∈ ((firstHalt marker payload oracle state trace input message
      initial terminal prior saved table cache).costed ()).support) :
    ((nativeWorldCallerEncoding (n := n) (κ := κ) ES).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, NativeCompressionCall.code, false, prior,
        code n marker payload, [], result.1)).length ≤
    encodedBound marker payload stateSize initial terminal prior state trace input message saved stateIncrement responseCap := by
  have reached := firstHalt_operational marker payload oracle state trace input message initial terminal prior saved table cache () result support
  have bounded := (firstHalt marker payload oracle state trace input message initial terminal prior saved table cache).bounded () result support
  change result.2 ≤ (whole marker payload oracle state trace input message initial terminal prior saved table cache).budget () at bounded
  rw [whole_budget_polynomial] at bounded
  exact whole_encoded_peak marker payload ES stateSize initial terminal prior state trace input message saved
    stateIncrement responseCap oracle hState hOracle result.1 result.2 bounded reached
end Foundation.Hash.Native.AdaptivePublicCaller
