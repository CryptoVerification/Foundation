import Foundation.Crypto.Semantics.ResourceSimulation
import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution
import Foundation.Crypto.Semantics.Oracle.ControllerStorageRelocation

/-! The complete private source controller instantiates the generic resource
simulation rule. Caller relocation preserves all retained data and actual
steps, so the same nonlinear memory bound is reused after code placement. -/
namespace CryptoOracle.Interactive.ControllerExtent
open Foundation.Probability
universe u
variable {State : Type u}

noncomputable def sourceEnvelope (stateSize : State → Nat) (native : Machine.Program)
    (code : Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap) :
    TimedExecution.ResourceGrowth.Envelope (OneUseSource.step native code oracle) where
  extent := sourceExtent stateSize
  retained := ControllerStorage.sourceCells stateSize
  bound := fun extent => 4 * extent ^ 2 + 11 * extent + 2
  monotone := by
    intro a b h
    have hp := Nat.pow_le_pow_left h 2
    change 4 * a ^ 2 + 11 * a + 2 ≤ 4 * b ^ 2 + 11 * b + 2
    omega
  covers := source_cells stateSize
  increment := stateIncrement + responseCap + 2
  grows := by
    intro start next h
    have hb := source_step stateSize native code oracle stateIncrement responseCap hOracle start next h
    omega

/-- The source proof supplies the whole resource envelope; placement supplies
only exact step simulation and the actual retained-data equality. Prefixes of
the leading instruction list are outside this entry and charged separately. -/
theorem relocated_peak (stateSize : State → Nat) (before code : Code)
    (native : Machine.Program) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseSource.step native (CodeRelocation.host before code) oracle) elapsed
      (CodeRelocation.oneUse before.length start)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      4 * (sourceExtent stateSize start + horizon * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (sourceExtent stateSize start + horizon * (stateIncrement + responseCap + 2)) + 2 := by
  exact (sourceEnvelope stateSize native code oracle stateIncrement responseCap hOracle).transport_peak
    (OneUseSource.step native (CodeRelocation.host before code) oracle)
    (CodeRelocation.oneUse before.length) (ControllerStorage.sourceCells stateSize)
    id (fun _ _ h => h)
    (fun source => le_of_eq (CodeRelocation.one_use_cells stateSize before.length source))
    (CodeRelocation.one_use_step before code native oracle) horizon elapsed hElapsed start target h

end CryptoOracle.Interactive.ControllerExtent
