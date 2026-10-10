import Foundation.Crypto.Semantics.Oracle.NativeCodeOracleIndependence
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentResources
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Full encoded storage for finite native-only interactive code.
The external capability is never used, so its internal resource behavior
needs no assumption. Bounds cover every supported physical frame. -/
namespace CryptoOracle.Interactive.NativeCode
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable {State : Type*}

private noncomputable def inertOracle : BitOracle State := fun state _ => PMF.pure (state, [])

def fullEncoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (ConfigurationEncoding.frame E)

def storageBound (program : Code) (initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap program + 3)
  2 * (EncodedStorage.codeEncoding.encode program).length + 144 * b ^ 2 + 372 * b + 173

/-- All supported intermediate states, including their full external state,
old history, finite code, physical table and both retained tape prefixes. -/
theorem encoded_peak_from (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State)
    (program : Code) (native : ∀ instruction ∈ program, ∃ op, instruction = .native op)
    (start : Configuration State) (valid : localControl start.control)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep program oracle)
      elapsed start).support) :
    ((fullEncoding E).encode (program, target)).length ≤
      storageBound program
        (NativePacketComponent.Resources.frameSize stateSize
          start) horizon := by
  rw [NativeCode.local_only_eval program native
    oracle inertOracle elapsed _ valid] at support
  have growth : ∀ state request result, result ∈ (inertOracle (State := State) state request).support →
      stateSize result.1 ≤ stateSize state + 0 ∧ result.2.length ≤ 0 := by
    intro state request result supported
    have same : result = (state, []) := by simpa [inertOracle] using supported
    subst result
    simp
  have bound := ResourceGrowth.prefix_bound
    (Reification.timedStep program inertOracle)
    (NativePacketComponent.Resources.frameSize stateSize)
    (NativePacketComponent.Resources.increment program 0 0)
    (NativePacketComponent.Resources.frame_step stateSize program inertOracle 0 0 growth)
    horizon elapsed within start
    target support
  have encoded := NativePacketComponent.Resources.frame_encoding_length E stateSize hState target
  simp only [NativePacketComponent.Resources.increment, Nat.add_zero] at bound
  have square := Nat.pow_le_pow_left bound 2
  simp only [fullEncoding, FiniteBitEncoding.prod_encode_length]
  dsimp only [storageBound]
  omega

/-- Backwards-compatible native running entry. -/
theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (program : Code) (native : ∀ instruction ∈ program, ∃ op, instruction = .native op)
    (machine : Machine.Configuration)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep program oracle)
      elapsed (NativeCode.frame state trace machine)).support) :
    ((fullEncoding E).encode (program, target)).length ≤
      storageBound program
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace machine)) horizon := by
  exact encoded_peak_from E stateSize hState oracle program native
    (NativeCode.frame state trace machine) (by trivial) horizon elapsed within target support

end CryptoOracle.Interactive.NativeCode
