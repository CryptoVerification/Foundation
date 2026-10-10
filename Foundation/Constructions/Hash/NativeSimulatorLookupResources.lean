import Foundation.Constructions.Hash.NativeSimulatorLookup
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources

/-! Full code, state, prior history and physical-tape encoding bounds for
native simulator-table lookup. External capabilities are unused; no resource
assumption on their internal computation is imposed. Encoded length is not
host RAM usage, and transition counts are not elapsed wall-clock time. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
variable {State : Type*}

def lookupEncoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (ConfigurationEncoding.frame E)

def lookupStorageBound (n κ initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap (lookupCode n κ) + 3)
  2 * (EncodedStorage.codeEncoding.encode (lookupCode n κ)).length + 144 * b ^ 2 + 372 * b + 173

/-- All supported intermediate states, including their full external state,
old history, finite code, physical table and both retained tape prefixes. -/
theorem lookup_encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput : List (Option Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      elapsed (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))).support) :
    ((lookupEncoding E).encode (lookupCode n κ, target)).length ≤
      lookupStorageBound n κ
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))) horizon := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace
    (lookupCode n κ) (lookupCode_native n κ) (scanStart table query beforeInput beforeOutput) horizon elapsed within target support

/-- The actual first-halt endpoint obeys the bound using its own reported
transition count, rather than charging a longer table-length budget. -/
theorem lookup_first_encoded (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration State × Nat)
    (support : result ∈ (runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (fun frame => Reification.terminal frame.control) (lookupSteps query table)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))).support) :
    ((lookupEncoding E).encode (lookupCode n κ, result.1)).length ≤
      lookupStorageBound n κ
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))) result.2 := by
  exact lookup_encoded_peak E stateSize hState oracle state trace query table beforeInput beforeOutput
    result.2 result.2 (Nat.le_refl _) result.1 (runToBoundary_reachable _ _ _ _ result support)

end Foundation.Hash.Native.SimulatorLookup
