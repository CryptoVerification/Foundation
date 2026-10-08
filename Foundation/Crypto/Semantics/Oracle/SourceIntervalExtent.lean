import Foundation.Crypto.Semantics.Oracle.OneUseSourceInterval
import Foundation.Crypto.Semantics.BoundaryResourceGrowth

/-! Ordinary caller intervals grow retained extent independently of an
external oracle's response cap: they stop before any oracle interaction. -/
namespace CryptoOracle.Interactive.OneUseSourceInterval
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

private noncomputable def emptyOracle : BitOracle State := fun state _ => PMF.pure (state, [])

private theorem empty_bound (stateSize : State → Nat) : ∀ state request result,
    result ∈ (emptyOracle state request).support →
      stateSize result.1 ≤ stateSize state + 0 ∧ result.2.length ≤ 0 := by
  intro state request result hs
  simp only [emptyOracle, PMF.mem_support_pure_iff] at hs
  subst result
  simp

/-- The actual oracle is not invoked before the interval boundary. -/
theorem oracle_independent (code : Code) (first second : BitOracle State) (frame : Configuration State)
    (hBoundary : boundary code frame.control = false) :
    Reification.timedStep code first frame = Reification.timedStep code second frame := by
  cases hc : frame.control with
  | running machine =>
      cases hi : code[machine.pc]? with
      | none => simp_all [boundary, Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition]
      | some instruction =>
          cases instruction with
          | call => simp_all [boundary]
          | native instruction =>
              cases hn : instruction.next machine <;>
                simp_all [boundary, Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition]
  | sending machine tape reversed =>
      cases ht : tape.current <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, hc, ht]
  | reversing machine remaining request =>
      cases remaining <;> simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, hc]
  | loading machine remaining tape =>
      cases remaining <;> simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, hc]
  | rewinding machine tape =>
      cases ht : tape.left <;> simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, hc, ht]
  | advancing machine remaining tape =>
      simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, hc]
  | awaiting machine request => simp [boundary, hc] at hBoundary
  | finished bit => simp [Reification.timedStep, Reification.terminal, hc]

theorem extent_step (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (store : Machine.Tape) (start next : Configuration State)
    (hBoundary : boundary code start.control = false)
    (hNext : next ∈ (Reification.timedStep code oracle start).support) :
    ControllerExtent.sourceExtent stateSize (embed spent store next) ≤
      ControllerExtent.sourceExtent stateSize (embed spent store start) + 2 := by
  rw [oracle_independent code oracle emptyOracle start hBoundary] at hNext
  have hb := ControllerExtent.public_step stateSize code emptyOracle 0 0 (empty_bound stateSize) start next hNext
  simp only [Nat.add_zero] at hb
  simp only [embed, ControllerExtent.sourceExtent]
  omega

/-- The actual arrival time, rather than the interval cap, bounds growth. -/
theorem extent_at_boundary (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (store : Machine.Tape) (fuel : Nat) (start : Configuration State)
    (result : Configuration State × Nat)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary code frame.control) fuel start).support) :
    ControllerExtent.sourceExtent stateSize (embed spent store result.1) ≤
      ControllerExtent.sourceExtent stateSize (embed spent store start) + result.2 * 2 :=
  ResourceGrowth.boundary_before (Reification.timedStep code oracle)
    (fun frame => boundary code frame.control)
    (fun frame => ControllerExtent.sourceExtent stateSize (embed spent store frame)) 2
    (fun start hs next hn => extent_step stateSize code oracle spent store start next hs hn) fuel start result h

theorem extent_cap (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (store : Machine.Tape) (fuel : Nat) (start : Configuration State)
    (result : Configuration State × Nat)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary code frame.control) fuel start).support) :
    ControllerExtent.sourceExtent stateSize (embed spent store result.1) ≤
      ControllerExtent.sourceExtent stateSize (embed spent store start) + fuel * 2 :=
  ResourceGrowth.boundary_before_cap (Reification.timedStep code oracle)
    (fun frame => boundary code frame.control)
    (fun frame => ControllerExtent.sourceExtent stateSize (embed spent store frame)) 2
    (fun start hs next hn => extent_step stateSize code oracle spent store start next hs hn) fuel start result h

end CryptoOracle.Interactive.OneUseSourceInterval
