import Foundation.Crypto.Semantics.Oracle.OneUseAllocation

/-! Complete storage growth through private generation and active execution.
Allocation counters are analysis certificates, not additional runtime code. -/
namespace CryptoOracle.Interactive.InitializationAllocation
open Foundation.Probability
universe u
variable {State : Type u}

def allowance (stateSize : State → Nat) (stateIncrement responseCap : Nat) :
    OneUseInitialization.Control State → Nat
  | .initializing _ => 0
  | .active source => OneUseAllocation.allowance stateSize stateIncrement responseCap source

theorem step_bound (stateSize : State → Nat) (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : OneUseInitialization.Control State)
    (h : next ∈ (OneUseInitialization.step generator native code oracle caller start).support) :
    ControllerStorage.initializationCells stateSize caller next ≤
      ControllerStorage.initializationCells stateSize caller start + allowance stateSize stateIncrement responseCap start + 2 := by
  cases start with
  | initializing component =>
      cases component <;> simp only [OneUseInitialization.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := Machine.ControllerStorage.initialization_local generator _ value hv
           simp only [ControllerStorage.initializationCells, allowance]
           omega)
        | (rw [PMF.mem_support_pure_iff] at h; subst next
           simp [ControllerStorage.initializationCells, ControllerStorage.sourceCells,
             Machine.ControllerStorage.initializationCells, allowance]
           omega)
  | active source =>
      rw [OneUseInitialization.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      exact OneUseAllocation.step_bound stateSize native code oracle stateIncrement responseCap hOracle source value hv

theorem prefix_certificate (stateSize : State → Nat) (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (elapsed : Nat) (start intermediate : OneUseInitialization.Control State)
    (h : intermediate ∈ (TimedExecution.eval (OneUseInitialization.step generator native code oracle caller) elapsed start).support) :
    ∃ allocated,
      (intermediate, allocated) ∈ (TimedExecution.eval
        (TimedExecution.AllocationCounter.step (OneUseInitialization.step generator native code oracle caller)
          (fun current => allowance stateSize stateIncrement responseCap current + 2))
        elapsed (start, 0)).support ∧
      ControllerStorage.initializationCells stateSize caller intermediate ≤
        ControllerStorage.initializationCells stateSize caller start + allocated :=
  TimedExecution.AllocationCounter.physical_prefix _ _ _
    (step_bound stateSize generator native code oracle caller stateIncrement responseCap hOracle) elapsed start intermediate h

/-- For a preserved invariant bounding copying, this covers every prefix of
the same machine from generation through rejection, encryption and return. -/
theorem peak (stateSize : State → Nat) (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (valid : OneUseInitialization.Control State → Prop) (copyCap : Nat)
    (hValid : ∀ start, valid start → ∀ next,
      next ∈ (OneUseInitialization.step generator native code oracle caller start).support → valid next)
    (hCopy : ∀ start, valid start → allowance stateSize stateIncrement responseCap start ≤ copyCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : OneUseInitialization.Control State) (hStart : valid start)
    (h : intermediate ∈ (TimedExecution.eval
      (OneUseInitialization.step generator native code oracle caller) elapsed start).support) :
    ControllerStorage.initializationCells stateSize caller intermediate ≤
      ControllerStorage.initializationCells stateSize caller start + horizon * (copyCap + 2) := by
  have hb := TimedExecution.ResourceGrowth.invariant_endpoint
    (OneUseInitialization.step generator native code oracle caller)
    (ControllerStorage.initializationCells stateSize caller) valid (copyCap + 2)
    (fun current hv next hn => ⟨hValid current hv next hn, by
      have hl := step_bound stateSize generator native code oracle caller stateIncrement responseCap hOracle current next hn
      have hc := hCopy current hv
      omega⟩) elapsed start intermediate hStart h
  have hm := Nat.mul_le_mul_right (copyCap + 2) hElapsed
  omega

end CryptoOracle.Interactive.InitializationAllocation
