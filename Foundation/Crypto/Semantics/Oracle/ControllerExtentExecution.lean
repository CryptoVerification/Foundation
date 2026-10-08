import Foundation.Crypto.Semantics.Oracle.ControllerExtent

/-! Extent grows by a constant at every real transition, including copies. -/
namespace CryptoOracle.Interactive.ControllerExtent
open Foundation.Probability
universe u
variable {State : Type u}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem public_step (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : Configuration State)
    (h : next ∈ (Reification.timedStep code oracle start).support) :
    frameExtent stateSize next ≤ frameExtent stateSize start +
      stateIncrement + responseCap + 2 := by
  rcases start with ⟨state, control, trace⟩
  have hTrace := trace_length trace
  cases control with
  | running machine =>
      cases hh : machine.halted with
      | true =>
          simp [Reification.timedStep, Reification.terminal, hh] at h
          subst next
          simp [frameExtent] <;> omega
      | false =>
          cases hi : code[machine.pc]? with
          | none =>
              simp [Reification.timedStep, Reification.terminal, Reification.perform,
                Reification.action, transition, hh, hi] at h
              subst next
              simp [frameExtent, controlExtent]
              omega
          | some instruction =>
              cases instruction with
              | call =>
                  simp [Reification.timedStep, Reification.terminal, Reification.perform,
                    Reification.action, transition, hh, hi] at h
                  subst next
                  simp [frameExtent, controlExtent,
                    Machine.Configuration.advance, Machine.ControllerExtent.machine] <;> omega
              | native instruction =>
                  cases hn : instruction.next machine with
                  | inl target =>
                      have hb := Machine.ControllerExtent.instruction_bound instruction machine target (by simp [hn])
                      simp [Reification.timedStep, Reification.terminal, Reification.perform,
                        Reification.action, transition, hh, hi, hn] at h
                      subst next
                      simp only [frameExtent, controlExtent]
                      omega
                  | inr pair =>
                      rcases pair with ⟨zero, one⟩
                      have hz := Machine.ControllerExtent.instruction_bound instruction machine zero (by simp [hn])
                      have ho := Machine.ControllerExtent.instruction_bound instruction machine one (by simp [hn])
                      simp only [Reification.timedStep, Reification.terminal, hh, Bool.false_eq_true,
                        ↓reduceIte, Reification.perform, Reification.action, transition, hi, hn,
                        PMF.mem_support_map_iff] at h
                      obtain ⟨bit, _, he⟩ := h
                      subst next
                      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte,
                        frameExtent, controlExtent] <;> omega
  | sending machine tape reversed =>
      cases ht : tape.current <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, ht] at h <;> subst next
      · simp [frameExtent, controlExtent]
        omega
      · have hb := Machine.Tape.cells_moveRight_le tape
        simp only [frameExtent, controlExtent, List.length_cons]
        omega
  | reversing machine remaining request =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;>
        simp [frameExtent, controlExtent] <;> omega
  | awaiting machine request =>
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.mem_support_map_iff] at h
      obtain ⟨result, hr, he⟩ := h
      subst next
      obtain ⟨hs, hl⟩ := hOracle state request result hr
      simp only [frameExtent, controlExtent, traceExtent,
        Machine.Tape.cells, List.length_nil]
      omega
  | loading machine remaining tape =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;>
        simp [frameExtent, controlExtent, Machine.Tape.cells_write] <;> omega
  | advancing machine remaining tape =>
      simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition] at h
      subst next
      have hb := Machine.Tape.cells_moveRight_le tape
      simp only [frameExtent, controlExtent]
      omega
  | rewinding machine tape =>
      cases hl : tape.left <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, hl] at h <;> subst next
      · simp [frameExtent, controlExtent, Machine.ControllerExtent.machine]
        omega
      · have hb := Machine.Tape.cells_moveLeft_le tape
        simp only [frameExtent, controlExtent]
        omega
  | finished bit =>
      simp [Reification.timedStep, Reification.terminal] at h
      subst next
      omega



def metadataExtent (stateSize : State → Nat) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Nat :=
  max (Machine.ControllerExtent.machine saved) (max (stateSize state) (max (traceExtent trace) request.length))

theorem callback_step (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : NativeCallback.Control State)
    (h : next ∈ (NativeCallback.step native code oracle saved state trace request start).support) :
    callbackExtent stateSize next ≤
      max (metadataExtent stateSize saved state trace request) (callbackExtent stateSize start) +
        (stateIncrement + responseCap + 2) := by
  cases start with
  | responding component =>
      cases component <;> simp only [NativeCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           have ht := trace_length trace
           simp only [callbackExtent, NativeCallback.loading, frameExtent, controlExtent, traceExtent,
             Machine.ControllerExtent.exportExtent, metadataExtent, Machine.Tape.cells, List.length_nil]
           omega)
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerExtent.export_bound native _ value hv
           simp only [callbackExtent]
           omega)
  | source frame =>
      rw [NativeCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      have hb := public_step stateSize code oracle stateIncrement responseCap hOracle frame value hv
      simp only [callbackExtent]
      omega


theorem checked_step (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : CheckedCallback.Control State)
    (h : next ∈ (CheckedCallback.step native code oracle saved state trace request start).support) :
    checkedExtent stateSize next ≤ max (metadataExtent stateSize saved state trace request) (checkedExtent stateSize start) +
      (stateIncrement + responseCap + 2) := by
  cases start with
  | preparing preparation =>
      cases preparation with
      | preparing pair =>
          cases pair <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_map_iff] at h
               obtain ⟨value, hv, he⟩ := h
               subst next
               have hb := Machine.ControllerExtent.check_bound _ value hv
               simp only [checkedExtent] at *
               omega)
            | (rw [PMF.mem_support_pure_iff] at h
               subst next
               simp [checkedExtent, Machine.ControllerExtent.check,
                 Machine.ControllerExtent.pair, Machine.ControllerExtent.exportExtent,
                 Machine.ControllerExtent.machine, Machine.Tape.cells]
               omega)
      | failure recovery =>
          cases recovery <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_map_iff] at h
               obtain ⟨value, hv, he⟩ := h
               subst next
               have hb := Machine.ControllerExtent.check_bound _ value hv
               simp only [checkedExtent] at *
               omega)
            | (rw [PMF.mem_support_pure_iff] at h
               subst next
               simp [checkedExtent, callbackExtent,
                 Machine.ControllerExtent.check, Machine.ControllerExtent.failure,
                 Machine.ControllerExtent.exportExtent, Machine.ControllerExtent.machine,
                 Machine.Tape.cells]
               omega)
  | computing first second component =>
      cases component <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerExtent.export_bound native _ value hv
           simp only [checkedExtent] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           simp [checkedExtent, Machine.ControllerExtent.packet,
             Machine.ControllerExtent.exportExtent] <;> omega)
  | tagging first second packet =>
      cases packet <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerExtent.packet_bound _ value hv
           simp only [checkedExtent] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           simp [checkedExtent, callbackExtent,
             Machine.ControllerExtent.packet, Machine.ControllerExtent.exportExtent,
             Machine.ControllerExtent.machine, Machine.Tape.cells]
           omega)
  | calling first second callback =>
      rw [CheckedCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      have hb := callback_step stateSize [] code oracle stateIncrement responseCap hOracle
        saved state trace request callback value hv
      simp only [checkedExtent]
      omega



theorem source_step (stateSize : State → Nat) (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : OneUseSource.Control State)
    (h : next ∈ (OneUseSource.step native code oracle start).support) :
    sourceExtent stateSize next ≤ sourceExtent stateSize start + (stateIncrement + responseCap + 2) := by
  cases start with
  | source used key frame =>
      rcases frame with ⟨state, control, trace⟩
      cases control <;> simp only [OneUseSource.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := public_step stateSize code oracle stateIncrement responseCap hOracle _ value hv
           simp only [sourceExtent, frameExtent, controlExtent] at *
           omega)
        | (cases used <;> try simp only [Bool.false_eq_true, ↓reduceIte] at h
           <;> rw [PMF.mem_support_pure_iff] at h <;> subst next
           <;> simp [sourceExtent, checkedExtent,
             Machine.ControllerExtent.check, Machine.ControllerExtent.pair,
             Machine.ControllerExtent.packet, frameExtent, controlExtent,
             Machine.Tape.cells, Machine.ControllerExtent.machine, metadataExtent] <;> omega)
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
                   have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
                     saved state trace request _ value hv
                   simp only [sourceExtent, metadataExtent] at *
                   omega)
                | (rw [PMF.mem_support_pure_iff] at h; subst next
                   simp [sourceExtent, checkedExtent,
                     Machine.ControllerExtent.check, Machine.ControllerExtent.pair,
                     Machine.ControllerExtent.packet, Machine.ControllerExtent.exportExtent,
                     Machine.ControllerExtent.machine, Machine.Tape.cells, metadataExtent]
                   omega)
          | failure recovery =>
              simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
              obtain ⟨value, hv, he⟩ := h
              subst next
              have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
                saved state trace request _ value hv
              simp only [sourceExtent, metadataExtent] at *
              omega
      | computing first second component =>
          simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨value, hv, he⟩ := h
          subst next
          have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
            saved state trace request _ value hv
          simp only [sourceExtent, metadataExtent] at *
          omega
      | tagging first second packet =>
          simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨value, hv, he⟩ := h
          subst next
          have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
            saved state trace request _ value hv
          simp only [sourceExtent, metadataExtent] at *
          omega
      | calling first second callback =>
          cases callback with
          | responding component =>
              simp only [OneUseSource.step, PMF.mem_support_map_iff] at h
              obtain ⟨value, hv, he⟩ := h
              subst next
              have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
                saved state trace request _ value hv
              simp only [sourceExtent, metadataExtent] at *
              omega
          | source frame =>
              rcases frame with ⟨newState, control, newTrace⟩
              cases control <;> simp only [OneUseSource.step] at h
              all_goals first
                | (rw [PMF.mem_support_map_iff] at h
                   obtain ⟨value, hv, he⟩ := h
                   subst next
                   have hb := checked_step stateSize native code oracle stateIncrement responseCap hOracle
                     saved state trace request _ value hv
                   simp only [sourceExtent, metadataExtent] at *
                   omega)
                | (rw [PMF.mem_support_pure_iff] at h; subst next
                   simp only [sourceExtent, checkedExtent,
                     callbackExtent, metadataExtent]
                   omega)



theorem initialization_step (stateSize : State → Nat) (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : OneUseInitialization.Control State)
    (h : next ∈ (OneUseInitialization.step generator native code oracle caller start).support) :
    initializationExtent stateSize caller next ≤
      initializationExtent stateSize caller start + (stateIncrement + responseCap + 2) := by
  cases start with
  | initializing component =>
      cases component <;> simp only [OneUseInitialization.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerExtent.initialization_bound generator _ value hv
           simp only [initializationExtent]
           omega)
        | (rw [PMF.mem_support_pure_iff] at h; subst next
           simp [initializationExtent, sourceExtent,
             Machine.ControllerExtent.initialization]
           omega)
  | active source =>
      rw [OneUseInitialization.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      exact source_step stateSize native code oracle stateIncrement responseCap hOracle source value hv


/-- A polynomial peak bound for the complete physical private controller.
No bound on copying is assumed: copying preserves extent, and every real
transition increases extent by at most the explicit oracle/interface bound. -/
theorem initialization_peak (stateSize : State → Nat) (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : OneUseInitialization.Control State)
    (h : intermediate ∈ (TimedExecution.eval
      (OneUseInitialization.step generator native code oracle caller) elapsed start).support) :
    ControllerStorage.initializationCells stateSize caller intermediate ≤
      4 * (initializationExtent stateSize caller start + horizon * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (initializationExtent stateSize caller start + horizon * (stateIncrement + responseCap + 2)) + 2 := by
  have he := Foundation.Probability.TimedExecution.ResourceGrowth.prefix_bound
    (OneUseInitialization.step generator native code oracle caller)
    (initializationExtent stateSize caller) (stateIncrement + responseCap + 2)
    (initialization_step stateSize generator native code oracle caller stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start intermediate h
  have hs := initialization_cells stateSize caller intermediate
  have hq := Nat.pow_le_pow_left he 2
  nlinarith

end CryptoOracle.Interactive.ControllerExtent
