import Foundation.Crypto.Semantics.Oracle.OneUseXorRequest
import Foundation.Crypto.Semantics.ProcedureInterval
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Ordinary instruction intervals of arbitrary finite caller code lift to
the one-use controller. Intervals stop before a call or at a real terminal
state. Local coins, tape movement, and the saved caller frame are retained;
no oracle response is fabricated by the interval proof. -/
namespace CryptoOracle.Interactive.OneUseSourceInterval
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def boundary (code : Code) : Control → Bool
  | .running machine => machine.halted || decide (code[machine.pc]? = some .call)
  | .awaiting _ _ => true
  | .finished _ => true
  | _ => false

def outerBoundary (code : Code) : OneUseSource.Control State → Bool
  | .source _ _ frame => boundary code frame.control
  | .handling _ _ _ _ _ _ => true

def embed (spent : Bool) (key : Machine.Tape) (frame : Configuration State) : OneUseSource.Control State :=
  .source spent key frame

variable (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape)

theorem step_embedding (frame : Configuration State) (h : boundary code frame.control = false) :
    OneUseSource.step native code oracle (embed spent key frame) =
      (Reification.timedStep code oracle frame).map (embed spent key) := by
  cases hc : frame.control <;> simp only [embed, OneUseSource.step, hc]
  all_goals first | rfl | simp [boundary, hc] at h

/-- Fuel bounds ordinary execution only. It does not assert that the next
call or halt is reached by that fuel. The endpoint and actual cost are joint. -/
noncomputable def interval (fuel : Nat) :=
  Procedure.interval (Reification.timedStep code oracle) (OneUseSource.step native code oracle)
    (fun frame => boundary code frame.control) (outerBoundary code) (embed spent key)
    (fun _ => rfl) (step_embedding native code oracle spent key) fuel

theorem costed (fuel : Nat) (frame : Configuration State) :
    (interval native code oracle spent key fuel).costed frame =
      runToBoundary (Reification.timedStep code oracle)
        (fun frame => boundary code frame.control) fuel frame := rfl

theorem budget (fuel : Nat) (frame : Configuration State) :
    (interval native code oracle spent key fuel).budget frame = fuel := rfl

/-- Each supported endpoint chooses its own handler/continuation contract.
Equality of the physical handoff is mandatory, including private key, tapes,
program counter, oracle state and history. Selection itself executes no code. -/
noncomputable def follow {Output : Type*} (fuel : Nat)
    (next : Configuration State → Procedure (OneUseSource.step native code oracle) Unit Output)
    (hEntry : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).entry () = embed spent key final)
    (cap : Configuration State → Nat)
    (hCap : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).budget () ≤ cap initial) :=
  (interval native code oracle spent key fuel).seq (Procedure.dispatch next) hEntry cap hCap

theorem follow_budget {Output : Type*} (fuel : Nat)
    (next : Configuration State → Procedure (OneUseSource.step native code oracle) Unit Output)
    (hEntry : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).entry () = embed spent key final)
    (cap : Configuration State → Nat)
    (hCap : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).budget () ≤ cap initial) (frame : Configuration State) :
    (follow native code oracle spent key fuel next hEntry cap hCap).budget frame = fuel + cap frame := rfl

theorem follow_costed {Output : Type*} (fuel : Nat)
    (next : Configuration State → Procedure (OneUseSource.step native code oracle) Unit Output)
    (hEntry : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).entry () = embed spent key final)
    (cap : Configuration State → Nat)
    (hCap : ∀ initial final, final ∈ ((interval native code oracle spent key fuel).semantics initial).support →
      (next final).budget () ≤ cap initial) (frame : Configuration State) :
    (follow native code oracle spent key fuel next hEntry cap hCap).costed frame =
      (runToBoundary (Reification.timedStep code oracle)
        (fun frame => boundary code frame.control) fuel frame).bind (fun returned =>
          ((next returned.1).costed ()).map (fun answer =>
            ((returned.1, answer.1), returned.2 + answer.2))) := rfl

/-- Arrival is derived from an explicit certificate about ordinary source
execution, rather than from the interval's finite fuel alone. -/
theorem complete (fuel : Nat) (frame : Configuration State)
    (hComplete : ∀ final ∈ (TimedExecution.eval (Reification.timedStep code oracle) fuel frame).support,
      boundary code final.control = true)
    (final : Configuration State)
    (hFinal : final ∈ ((interval native code oracle spent key fuel).semantics frame).support) :
    boundary code final.control = true :=
  Procedure.interval_complete (Reification.timedStep code oracle) (OneUseSource.step native code oracle)
    (fun frame => boundary code frame.control) (outerBoundary code) (embed spent key) (fun _ => rfl)
    (step_embedding native code oracle spent key) fuel frame hComplete final hFinal

/-- Instruction intervals obey the same whole-controller memory measure as
query handlers. No caller tape or saved transcript is omitted at the entry. -/
theorem memory_peak (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (fuel elapsed : Nat) (hElapsed : elapsed ≤ fuel) (frame : Configuration State)
    (target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval (OneUseSource.step native code oracle)
      elapsed (embed spent key frame)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      4 * (ControllerExtent.sourceExtent stateSize (embed spent key frame) +
        fuel * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.sourceExtent stateSize (embed spent key frame) +
        fuel * (stateIncrement + responseCap + 2)) + 2 :=
  (ControllerExtent.sourceEnvelope stateSize native code oracle
    stateIncrement responseCap hOracle).peak fuel elapsed hElapsed _ target h

end CryptoOracle.Interactive.OneUseSourceInterval
