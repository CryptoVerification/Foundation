import Foundation.Crypto.Semantics.KeyedIteration
import Foundation.Examples.RejectionTiming

/-! Rejection preserves an arbitrary prior key distribution, jointly with
the actual public return and cost of a real caller invocation. The request
and initial public configuration are fixed independently of the key. -/
namespace Foundation.Examples.RejectionKeyDistribution
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
universe u v

theorem joint_independence {State : Type u} {width : Nat} (keys : PMF (Bits width))
    (native : Bits width → Machine.Program) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (tail : List (Option Bool))
    (hMismatch : width ≠ request.length) :
    KeyedIteration.joint keys (fun key =>
      RejectionTiming.publicRun (native key) oracle state trace key request tail hMismatch) =
      keys.bind (fun key =>
        (RejectionTiming.publicRun [] oracle state trace (fun _ => false) request tail hMismatch).map
          (fun result => (key, result))) := by
  apply KeyedIteration.joint_independent
  intro key
  exact RejectionTiming.key_independence (native key) [] oracle state trace key
    (fun _ => false) request tail hMismatch

/-- An arbitrary probabilistic observation of the public frame and actual
cost also leaves the prior as an independent factor. -/
theorem observer_independence {State : Type u} {Observed : Type v} {width : Nat}
    (keys : PMF (Bits width)) (native : Bits width → Machine.Program)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (tail : List (Option Bool)) (hMismatch : width ≠ request.length)
    (observer : Option (Configuration State) × Nat → PMF Observed) :
    (KeyedIteration.joint keys (fun key =>
      RejectionTiming.publicRun (native key) oracle state trace key request tail hMismatch)).bind
        (fun result => (observer result.2).map (fun seen => (result.1, seen))) =
      keys.bind (fun key =>
        ((RejectionTiming.publicRun [] oracle state trace (fun _ => false) request tail hMismatch).bind observer).map
          (fun seen => (key, seen))) := by
  apply KeyedIteration.joint_observe
  intro key
  exact RejectionTiming.key_independence (native key) [] oracle state trace key
    (fun _ => false) request tail hMismatch

end Foundation.Examples.RejectionKeyDistribution
