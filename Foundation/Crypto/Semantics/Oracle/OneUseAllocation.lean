import Foundation.Crypto.Semantics.Oracle.CheckedAllocation
import Foundation.Crypto.Semantics.AllocationCounter

/-! Complete one-use controller allocation: request capture, response return,
all component phases, and actual source resumption. Oracle assumptions are
explicit even for arbitrary malformed callback states. -/
namespace CryptoOracle.Interactive.OneUseAllocation
open Foundation.Probability
universe u
variable {State : Type u}

def allowance (stateSize : State → Nat) (stateIncrement responseCap : Nat) : OneUseSource.Control State → Nat
  | .source _ _ frame => match frame.control with
    | .awaiting saved _ => saved.outputTape.cells
    | _ => SourceAllocation.allowance stateIncrement responseCap frame.control
  | .handling _ saved state trace request handler =>
      CheckedAllocation.allowance stateSize stateIncrement responseCap saved state trace request handler

theorem step_bound (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : OneUseSource.Control State)
    (h : next ∈ (OneUseSource.step native code oracle start).support) :
    ControllerStorage.sourceCells stateSize next ≤ ControllerStorage.sourceCells stateSize start +
      allowance stateSize stateIncrement responseCap start + 2 := by
  cases start with
  | source used key frame =>
      rcases frame with ⟨state, control, trace⟩
      cases control <;> simp only [OneUseSource.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := SourceAllocation.step_bound stateSize code oracle stateIncrement responseCap hOracle _ value hv
           simp only [ControllerStorage.sourceCells, allowance, SourceAllocation.allowance] at *
           omega)
        | (cases used <;> try simp only [Bool.false_eq_true, ↓reduceIte] at h
           <;> rw [PMF.mem_support_pure_iff] at h <;> subst next
           <;> simp [ControllerStorage.sourceCells, ControllerStorage.checkedCells,
             Machine.ControllerStorage.checkCells, Machine.ControllerStorage.pairCells,
             Machine.ControllerStorage.packetCells, SourceStorage.cells, SourceStorage.controlCells,
             Machine.Tape.cells, allowance] <;> omega)
  | handling used saved state trace request handler =>
      cases handler with
      | preparing preparation =>
          cases preparation with
          | preparing pair =>
              cases pair <;> cases used <;> simp only [OneUseSource.step, Bool.false_eq_true, ↓reduceIte] at h
              all_goals first
                | (rw [PMF.mem_support_map_iff] at h
                   obtain ⟨value, hv, he⟩ := h
                   subst next
                   have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
                     saved state trace request _ value hv
                   simp only [ControllerStorage.sourceCells, allowance]
                   omega)
                | (rw [PMF.mem_support_pure_iff] at h; subst next
                   simp [ControllerStorage.sourceCells, ControllerStorage.checkedCells,
                     Machine.ControllerStorage.checkCells, Machine.ControllerStorage.pairCells,
                     Machine.ControllerStorage.packetCells, Machine.ControllerStorage.exportCells,
                     CheckedAllocation.allowance, Machine.Configuration.tapeCells, Machine.Tape.cells, allowance]
                   omega)
          | failure recovery =>
              simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
              obtain ⟨value, hv, he⟩ := h
              subst next
              have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
                saved state trace request _ value hv
              simp only [ControllerStorage.sourceCells, allowance]
              omega
      | computing first second component =>
          simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨value, hv, he⟩ := h
          subst next
          have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
            saved state trace request _ value hv
          simp only [ControllerStorage.sourceCells, allowance]
          omega
      | tagging first second packet =>
          simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨value, hv, he⟩ := h
          subst next
          have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
            saved state trace request _ value hv
          simp only [ControllerStorage.sourceCells, allowance]
          omega
      | calling first second callback =>
          cases callback with
          | responding component =>
              simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
              obtain ⟨value, hv, he⟩ := h
              subst next
              have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
                saved state trace request _ value hv
              simp only [ControllerStorage.sourceCells, allowance]
              omega
          | source frame =>
              rcases frame with ⟨newState, control, newTrace⟩
              cases control <;> simp only [OneUseSource.step] at h
              all_goals first
                | (rw [PMF.mem_support_map_iff] at h
                   obtain ⟨value, hv, he⟩ := h
                   subst next
                   have hb := CheckedAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle
                     saved state trace request _ value hv
                   simp only [ControllerStorage.sourceCells, allowance]
                   omega)
                | (rw [PMF.mem_support_pure_iff] at h; subst next
                   simp only [ControllerStorage.sourceCells, ControllerStorage.checkedCells,
                     ControllerStorage.callbackCells, allowance]
                   omega)

theorem prefix_certificate (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (elapsed : Nat) (start intermediate : OneUseSource.Control State)
    (h : intermediate ∈ (TimedExecution.eval (OneUseSource.step native code oracle) elapsed start).support) :
    ∃ allocated,
      (intermediate, allocated) ∈ (TimedExecution.eval
        (TimedExecution.AllocationCounter.step (OneUseSource.step native code oracle)
          (fun current => allowance stateSize stateIncrement responseCap current + 2))
        elapsed (start, 0)).support ∧
      ControllerStorage.sourceCells stateSize intermediate ≤ ControllerStorage.sourceCells stateSize start + allocated :=
  TimedExecution.AllocationCounter.physical_prefix _ _ _
    (step_bound stateSize native code oracle stateIncrement responseCap hOracle) elapsed start intermediate h

/-- A reachable-state invariant bounds the size of bulk copies. Combined
with the complete local law, it yields a peak bound for the whole machine. -/
theorem peak (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (valid : OneUseSource.Control State → Prop) (copyCap : Nat)
    (hValid : ∀ start, valid start → ∀ next, next ∈ (OneUseSource.step native code oracle start).support → valid next)
    (hCopy : ∀ start, valid start → allowance stateSize stateIncrement responseCap start ≤ copyCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : OneUseSource.Control State) (hStart : valid start)
    (h : intermediate ∈ (TimedExecution.eval (OneUseSource.step native code oracle) elapsed start).support) :
    ControllerStorage.sourceCells stateSize intermediate ≤
      ControllerStorage.sourceCells stateSize start + horizon * (copyCap + 2) := by
  have hb := TimedExecution.ResourceGrowth.invariant_endpoint (OneUseSource.step native code oracle)
    (ControllerStorage.sourceCells stateSize) valid (copyCap + 2)
    (fun current hv next hn => ⟨hValid current hv next hn, by
      have hl := step_bound stateSize native code oracle stateIncrement responseCap hOracle current next hn
      have hc := hCopy current hv
      omega⟩) elapsed start intermediate hStart h
  have hm := Nat.mul_le_mul_right (copyCap + 2) hElapsed
  omega

end CryptoOracle.Interactive.OneUseAllocation
