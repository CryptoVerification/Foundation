import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution
import Foundation.Crypto.Semantics.ResourceEnvelope

/-! The original private controller and other cryptographic controllers use
one resource-envelope interface. Boundary bounds retain actual elapsed cost. -/
namespace CryptoOracle.Interactive.ControllerExtent
open Foundation.Probability
universe u
variable {State : Type u}

noncomputable def initializationEnvelope (stateSize : State → Nat)
    (generator native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap) :
    TimedExecution.ResourceGrowth.Envelope
      (OneUseInitialization.step generator native code oracle caller) where
  extent := initializationExtent stateSize caller
  retained := ControllerStorage.initializationCells stateSize caller
  bound := fun extent => 4 * extent ^ 2 + 11 * extent + 2
  monotone := by
    intro a b h
    have hp := Nat.pow_le_pow_left h 2
    change 4 * a ^ 2 + 11 * a + 2 ≤ 4 * b ^ 2 + 11 * b + 2
    omega
  covers := initialization_cells stateSize caller
  increment := stateIncrement + responseCap + 2
  grows := initialization_step stateSize generator native code oracle caller stateIncrement responseCap hOracle

/-- The actual early boundary, including all retained copies, is bounded by
its elapsed transition count rather than the declared maximum fuel. -/
theorem initialization_boundary_cells (stateSize : State → Nat)
    (generator native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (boundary : OneUseInitialization.Control State → Bool) (fuel : Nat)
    (start : OneUseInitialization.Control State) (result : OneUseInitialization.Control State × Nat)
    (h : result ∈ (TimedExecution.runToBoundary
      (OneUseInitialization.step generator native code oracle caller) boundary fuel start).support) :
    ControllerStorage.initializationCells stateSize caller result.1 ≤
      4 * (initializationExtent stateSize caller start + result.2 * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (initializationExtent stateSize caller start + result.2 * (stateIncrement + responseCap + 2)) + 2 :=
  (initializationEnvelope stateSize generator native code oracle caller stateIncrement responseCap hOracle).at_boundary
    boundary fuel start result h

end CryptoOracle.Interactive.ControllerExtent
