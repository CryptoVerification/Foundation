import Foundation.Crypto.Semantics.Oracle.ReusableInitializationStorage
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseResources

/-! Initialization through arbitrary repeated requests uses one retained-data
bound. Generation code and handler code are arbitrary finite programs. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Initialized
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
abbrev Control (State : Type u) := ReusableResponseInitialization.Control ResponseHandoff.Control State
noncomputable abbrev step {State : Type u} (generator native : Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) :=
  ReusableResponseInitialization.step (ResponseHandoffProgram.step native) ReusableResponse.begin
    ResponseHandoffProgram.Callback.ready generator native code oracle caller

namespace Resources
open PrivacyStorage
variable {State : Type u} (stateSize : State → Nat) (caller : Configuration State)
abbrev cells := ReusableInitializationStorage.cells responderCells stateSize caller
abbrev extent := ReusableInitializationStorage.extent responderExtent stateSize caller

theorem cells_bound (c : Control State) :
    cells stateSize caller c ≤ 6 * (extent stateSize caller c) ^ 2 + 18 * extent stateSize caller c + 2 :=
  ReusableInitializationStorage.cells_bound responderCells responderExtent stateSize caller 3 0 responder_cells c

variable (generator native : Program) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hOracle in
theorem extent_step (start target : Control State)
    (h : target ∈ (step generator native code oracle caller start).support) :
    extent stateSize caller target ≤ extent stateSize caller start + (stateIncrement + responseCap + 5) := by
  have hb := ReusableInitializationStorage.extent_step responderExtent stateSize caller
    (ResponseHandoffProgram.step native) ReusableResponse.begin ResponseHandoffProgram.Callback.ready
    generator native code oracle (stateIncrement + responseCap + 4)
    (ReusableResponse.Resources.extent_step stateSize native code oracle stateIncrement responseCap hOracle) start target h
  simpa only [Nat.add_assoc] using hb

include hOracle in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : Control State)
    (hTarget : target ∈ (TimedExecution.eval (step generator native code oracle caller) elapsed start).support) :
    cells stateSize caller target ≤ ReusableInitializationStorage.bound
      (extent stateSize caller start) horizon (stateIncrement + responseCap + 4) 3 0 :=
  ReusableInitializationStorage.peak responderCells responderExtent stateSize caller 3 0 responder_cells
    (ResponseHandoffProgram.step native) ReusableResponse.begin ResponseHandoffProgram.Callback.ready
    generator native code oracle (stateIncrement + responseCap + 4)
    (ReusableResponse.Resources.extent_step stateSize native code oracle stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start target hTarget

end Resources
end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Initialized
