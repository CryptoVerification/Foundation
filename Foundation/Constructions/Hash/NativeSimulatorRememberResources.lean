import Foundation.Constructions.Hash.NativeSimulatorRemember
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources

/-! Full encoded storage bounds for physical simulator-table prepending.
Counts include finite code, both tapes, old table, external state and history
at every supported intermediate state. Layout preparation is outside entry.
Encoded length is not host RAM use; transitions are not wall-clock time. -/
namespace Foundation.Hash.Native.SimulatorRemember
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
variable {State : Type*}

def encoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (ConfigurationEncoding.frame E)

def storageBound (n κ initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap (code n κ) + 3)
  2 * (EncodedStorage.codeEncoding.encode (code n κ)).length + 144 * b ^ 2 + 372 * b + 173

/-- All supported intermediate states, including their full external state,
old history, finite code, physical table and both retained tape prefixes. -/
theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      elapsed (NativeCode.frame state trace (start entry table beforeOutput))).support) :
    ((encoding E).encode (code n κ, target)).length ≤
      storageBound n κ
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (start entry table beforeOutput))) horizon := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace
    (code n κ) (code_native n κ) (start entry table beforeOutput) horizon elapsed within target support

/-- The actual first-halt endpoint obeys the bound using its own reported
transition count, rather than charging a longer table-length budget. -/
theorem first_encoded (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (result : Configuration State × Nat)
    (support : result ∈ (runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps n κ)
      (NativeCode.frame state trace (start entry table beforeOutput))).support) :
    ((encoding E).encode (code n κ, result.1)).length ≤
      storageBound n κ
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (start entry table beforeOutput))) result.2 := by
  exact encoded_peak E stateSize hState oracle state trace entry table beforeOutput
    result.2 result.2 (Nat.le_refl _) result.1 (runToBoundary_reachable _ _ _ _ result support)

end Foundation.Hash.Native.SimulatorRemember
