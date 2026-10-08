import Foundation.Crypto.Semantics.Oracle.CallbackAllocation

/-! Storage growth across preparation, native computation, packet tagging,
and callback handoff. Actual copying transitions carry explicit allowances. -/
namespace CryptoOracle.Interactive.CheckedAllocation
open Foundation.Probability
universe u
variable {State : Type u}

def allowance (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : CheckedCallback.Control State → Nat
  | .calling _ _ callback =>
      CallbackAllocation.allowance stateSize stateIncrement responseCap saved state trace request callback
  | _ => 0

theorem step_bound (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : CheckedCallback.Control State)
    (h : next ∈ (CheckedCallback.step native code oracle saved state trace request start).support) :
    ControllerStorage.checkedCells stateSize next ≤ ControllerStorage.checkedCells stateSize start +
      allowance stateSize stateIncrement responseCap saved state trace request start + 2 := by
  cases start with
  | preparing preparation =>
      cases preparation with
      | preparing pair =>
          cases pair <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_map_iff] at h
               obtain ⟨value, hv, he⟩ := h
               subst next
               have hb := Machine.ControllerStorage.check_local _ value hv
               simp only [ControllerStorage.checkedCells, allowance] at *
               omega)
            | (rw [PMF.mem_support_pure_iff] at h
               subst next
               simp [ControllerStorage.checkedCells, Machine.ControllerStorage.checkCells,
                 Machine.ControllerStorage.pairCells, Machine.ControllerStorage.exportCells,
                 Machine.Configuration.tapeCells, Machine.Tape.cells, allowance]
               omega)
      | failure recovery =>
          cases recovery <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_map_iff] at h
               obtain ⟨value, hv, he⟩ := h
               subst next
               have hb := Machine.ControllerStorage.check_local _ value hv
               simp only [ControllerStorage.checkedCells, allowance] at *
               omega)
            | (rw [PMF.mem_support_pure_iff] at h
               subst next
               simp [ControllerStorage.checkedCells, ControllerStorage.callbackCells,
                 Machine.ControllerStorage.checkCells, Machine.ControllerStorage.failureCells,
                 Machine.ControllerStorage.exportCells, Machine.Configuration.tapeCells,
                 Machine.Tape.cells, allowance]
               omega)
  | computing first second component =>
      cases component <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerStorage.export_local native _ value hv
           simp only [ControllerStorage.checkedCells, allowance] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           simp [ControllerStorage.checkedCells, Machine.ControllerStorage.packetCells,
             Machine.ControllerStorage.exportCells, allowance])
  | tagging first second packet =>
      cases packet <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerStorage.packet_local _ value hv
           simp only [ControllerStorage.checkedCells, allowance] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           simp [ControllerStorage.checkedCells, ControllerStorage.callbackCells,
             Machine.ControllerStorage.packetCells, Machine.ControllerStorage.exportCells,
             Machine.Configuration.tapeCells, Machine.Tape.cells, allowance]
           omega)
  | calling first second callback =>
      rw [CheckedCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      have hb := CallbackAllocation.step_bound stateSize [] code oracle stateIncrement responseCap hOracle
        saved state trace request callback value hv
      simp only [ControllerStorage.checkedCells, allowance]
      omega

end CryptoOracle.Interactive.CheckedAllocation
