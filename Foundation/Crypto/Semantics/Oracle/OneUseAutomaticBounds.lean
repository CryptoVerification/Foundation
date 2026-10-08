import Foundation.Crypto.Semantics.Oracle.SourceIntervalExtent
import Foundation.Crypto.Semantics.Oracle.OneUseRoundsResources

/-! Derive request-size and query-time caps from the actual caller extent
and ordinary instruction fuel. No separate request cap or external oracle
response bound is needed to construct the round's execution contract. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

variable (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem request_extent (source : Boundary State) (data : CallLayout code source.frame) :
    data.request.length ≤ ControllerExtent.sourceExtent stateSize
      (embed (Machine.PairPreparation.operand [] key keyTail) source) := by
  have ht : data.request.length ≤ data.machine.outputTape.cells := by
    rw [data.tape, RequestExport.packetTape_cells]
    omega
  simp only [embed, ControllerExtent.sourceExtent, ControllerExtent.frameExtent,
    data.control, ControllerExtent.controlExtent, Machine.ControllerExtent.machine]
  omega

theorem caller_extent (fuel : Nat) (source result : Boundary State)
    (h : result ∈ ((caller code oracle key keyTail fuel).semantics source).support) :
    ControllerExtent.sourceExtent stateSize (embed (Machine.PairPreparation.operand [] key keyTail) result) ≤
      ControllerExtent.sourceExtent stateSize (embed (Machine.PairPreparation.operand [] key keyTail) source) + fuel * 2 := by
  change result ∈ (((runToBoundary (Reification.timedStep code oracle)
    (fun frame => OneUseSourceInterval.boundary code frame.control) fuel source.frame).map Prod.fst).map
      (fun frame => Boundary.mk source.spent frame)).support at h
  rw [PMF.map_comp, PMF.mem_support_map_iff] at h
  obtain ⟨returned, hReturned, he⟩ := h
  subst result
  exact OneUseSourceInterval.extent_cap stateSize code oracle source.spent
    (Machine.PairPreparation.operand [] key keyTail) fuel source.frame returned hReturned

def requestCap (fuel : Nat) (source : Boundary State) : Nat :=
  ControllerExtent.sourceExtent stateSize (embed (Machine.PairPreparation.operand [] key keyTail) source) + fuel * 2

theorem request_bound (fuel : Nat) (source result : Boundary State)
    (h : result ∈ ((caller code oracle key keyTail fuel).semantics source).support)
    (data : CallLayout code result.frame) : data.request.length ≤ requestCap stateSize key keyTail fuel source :=
  (request_extent stateSize code key keyTail result data).trans
    (caller_extent stateSize code oracle key keyTail fuel source result h)

/-- Every supported interval return is covered, including malformed request
lengths and already-used keys. The original finite VM still performs checks. -/
noncomputable def automaticRound (fuel : Nat) :=
  boundedRound code oracle key keyTail fuel (requestCap stateSize key keyTail fuel)
    (request_bound stateSize code oracle key keyTail fuel)

theorem automaticRound_budget (fuel : Nat) (source : Boundary State) :
    (automaticRound stateSize code oracle key keyTail fuel).budget source =
      fuel + (33 * (key.length + requestCap stateSize key keyTail fuel source) + 33) := rfl

/-- A uniform extent bound on admissible states yields a uniform round cap;
there is no additional per-query response-length assumption to discharge. -/
theorem automaticRound_uniform (fuel extentCap : Nat) (source : Boundary State)
    (hExtent : ControllerExtent.sourceExtent stateSize
      (embed (Machine.PairPreparation.operand [] key keyTail) source) ≤ extentCap) :
    (automaticRound stateSize code oracle key keyTail fuel).budget source ≤
      fuel + (33 * (key.length + extentCap + fuel * 2) + 33) := by
  rw [automaticRound_budget]
  unfold requestCap
  omega

end CryptoOracle.Interactive.OneUseSourceRounds
