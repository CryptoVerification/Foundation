import Foundation.Crypto.Semantics.Oracle.SourceAllocation

/-! Allocation at callback handoffs includes the new copy of the suspended
caller, oracle state, old transcript, request, and returned response. -/
namespace CryptoOracle.Interactive.CallbackAllocation
open Foundation.Probability
universe u
variable {State : Type u}

def allowance (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : NativeCallback.Control State → Nat
  | .responding (.returned packet) =>
      saved.tapeCells + stateSize state + SourceStorage.traceCells trace + request.length + packet.length
  | .source frame => SourceAllocation.allowance stateIncrement responseCap frame.control
  | _ => 0

theorem step_bound (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : NativeCallback.Control State)
    (h : next ∈ (NativeCallback.step native code oracle saved state trace request start).support) :
    ControllerStorage.callbackCells stateSize next ≤ ControllerStorage.callbackCells stateSize start +
      allowance stateSize stateIncrement responseCap saved state trace request start + 2 := by
  cases start with
  | responding component =>
      cases component <;> simp only [NativeCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           simp [ControllerStorage.callbackCells, NativeCallback.loading, SourceStorage.cells,
             SourceStorage.controlCells, SourceStorage.traceCells, Machine.ControllerStorage.exportCells,
             allowance, Machine.Tape.cells]
           omega)
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerStorage.export_local native _ value hv
           simpa only [ControllerStorage.callbackCells, allowance, Nat.add_zero] using hb)
  | source frame =>
      rw [NativeCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      exact SourceAllocation.step_bound stateSize code oracle stateIncrement responseCap hOracle frame value hv

end CryptoOracle.Interactive.CallbackAllocation
