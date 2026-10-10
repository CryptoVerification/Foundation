import Foundation.Crypto.Semantics.Oracle.NativePacketComponentOracleIndependence
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentResources
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Encoded storage for native-only computation and physical response export,
including the complete retained frame and the exporter's working state. -/
namespace CryptoOracle.Interactive.NativePacketComponent
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable {State : Type*}

private noncomputable def inertOracle : BitOracle State := fun state _ => PMF.pure (state, [])

def fullEncoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (Resources.encoding E)

def storageBound (program : Code) (initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap program + 3)
  2 * (EncodedStorage.codeEncoding.encode program).length + 512 * b ^ 2 + 1024 * b + 513

/-- All supported intermediate states of native computation and export.
The external capability is arbitrary and unused, not a source of hidden
sampling or table operations. Validity is preserved by native_only_step. -/
theorem encoded_peak_from (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (program : Code)
    (native : ∀ instruction ∈ program, ∃ op, instruction = .native op)
    (start : Control State) (valid : localControl start)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Control State)
    (support : target ∈ (TimedExecution.eval (step program oracle) elapsed start).support) :
    ((fullEncoding E).encode (program, target)).length ≤
      storageBound program (Resources.size stateSize start) horizon := by
  rw [local_only_eval program native oracle inertOracle elapsed start valid] at support
  have growth : ∀ state request result, result ∈ (inertOracle (State := State) state request).support →
      stateSize result.1 ≤ stateSize state + 0 ∧ result.2.length ≤ 0 := by
    intro state request result supported
    have same : result = (state, []) := by simpa [inertOracle] using supported
    subst result
    simp
  have bound := ResourceGrowth.prefix_bound (step program inertOracle) (Resources.size stateSize)
    (Resources.increment program 0 0)
    (Resources.step_size stateSize program inertOracle 0 0 growth)
    horizon elapsed within start target support
  have encoded := Resources.encoding_length E stateSize hState target
  simp only [Resources.increment, Nat.add_zero] at bound
  have square := Nat.pow_le_pow_left bound 2
  simp only [fullEncoding, FiniteBitEncoding.prod_encode_length]
  dsimp only [storageBound]
  omega

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (program : Code)
    (native : ∀ instruction ∈ program, ∃ op, instruction = .native op)
    (start : Control State) (valid : nativeControl start)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Control State)
    (support : target ∈ (TimedExecution.eval (step program oracle) elapsed start).support) :
    ((fullEncoding E).encode (program, target)).length ≤
      storageBound program (Resources.size stateSize start) horizon :=
  encoded_peak_from E stateSize hState oracle program native start (nativeControl_local start valid)
    horizon elapsed within target support

/-- Every actual first-arrival endpoint satisfies the same peak bound. -/
theorem first_encoded (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (program : Code)
    (native : ∀ instruction ∈ program, ∃ op, instruction = .native op)
    (start : Control State) (valid : nativeControl start) (boundary : Control State → Bool)
    (horizon : Nat) (result : Control State × Nat)
    (support : result ∈ (runToBoundary (step program oracle) boundary horizon start).support) :
    ((fullEncoding E).encode (program, result.1)).length ≤
      storageBound program (Resources.size stateSize start) horizon := by
  exact encoded_peak E stateSize hState oracle program native start valid horizon result.2
    (runToBoundary_bounded _ _ _ _ result support) result.1
    (runToBoundary_reachable _ _ _ _ result support)

end CryptoOracle.Interactive.NativePacketComponent
