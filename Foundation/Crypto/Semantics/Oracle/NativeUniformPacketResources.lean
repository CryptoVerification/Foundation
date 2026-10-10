import Foundation.Crypto.Semantics.Oracle.NativeUniformPacket
import Foundation.Crypto.Semantics.Oracle.NativePacketCodeResources
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Full code/frame/exporter representation bounds for the local native
sampler. The unused capability is fixed to a deterministic inert operation;
there is no hidden oracle table or sampling work behind that operation. -/
namespace CryptoOracle.Interactive.NativeUniformPacket
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type*}

noncomputable def silentOracle : BitOracle State := fun state _ => PMF.pure (state, [])

def completeEncoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (NativePacketComponent.Resources.encoding E)

def storageBound (initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap code + 3)
  2 * (EncodedStorage.codeEncoding.encode code).length + 512 * b ^ 2 + 1024 * b + 513

/-- Every represented cell and both the retained native frame and physical
exporter are counted, at every supported time up to the chosen horizon. -/
theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (width : Nat) (state : State) (prior : List (List Bool × List Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon)
    (target : NativePacketComponent.Control State)
    (support : target ∈ (TimedExecution.eval
      (NativePacketComponent.step code silentOracle) elapsed
      (.computing (start width state prior))).support) :
    ((completeEncoding E).encode (code, target)).length ≤
      storageBound (NativePacketComponent.Resources.size stateSize
        (.computing (start width state prior))) horizon := by
  have native : ∀ instruction ∈ code, ∃ op, instruction = .native op := by
    intro instruction member
    simp only [code, NativeCode.code, List.mem_map] at member
    obtain ⟨op, _, rfl⟩ := member
    exact ⟨_, rfl⟩
  exact NativePacketComponent.encoded_peak E stateSize hState silentOracle code native
    (.computing (start width state prior)) (by trivial) horizon elapsed within target support

/-- The joint actual first-return endpoint obeys the same full peak bound. -/
theorem first_return_encoded (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (width : Nat) (state : State) (prior : List (List Bool × List Bool))
    (result : NativePacketComponent.Control State × Nat)
    (support : result ∈ (runToBoundary (NativePacketComponent.step code silentOracle)
      NativePacketComponent.readyBoundary (8 * width + 7)
      (.computing (start width state prior))).support) :
    ((completeEncoding E).encode (code, result.1)).length ≤
      storageBound (NativePacketComponent.Resources.size stateSize
        (.computing (start width state prior))) (8 * width + 7) := by
  exact encoded_peak E stateSize hState width state prior (8 * width + 7) result.2
    (runToBoundary_bounded _ _ _ _ result support) result.1
    (runToBoundary_reachable _ _ _ _ result support)

end CryptoOracle.Interactive.NativeUniformPacket
