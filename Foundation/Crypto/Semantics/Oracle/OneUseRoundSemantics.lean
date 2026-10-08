import Foundation.Crypto.Semantics.Oracle.OneUseAutomaticBounds
import Foundation.Crypto.Semantics.BoundaryReachability

/-! Calculation rules for ordinary boundaries, physical query layouts and
actual terminals. These rules allow finite-code certificates to be proved
without unfolding the entire resource-contract construction. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem caller_at_boundary (fuel : Nat) (source : Boundary State)
    (hBoundary : OneUseSourceInterval.boundary code source.frame.control = true) :
    (caller code oracle key keyTail fuel).semantics source = PMF.pure source := by
  change ((runToBoundary (Reification.timedStep code oracle)
    (fun frame => OneUseSourceInterval.boundary code frame.control) fuel source.frame).map Prod.fst).map
      (fun frame => Boundary.mk source.spent frame) = _
  rw [runToBoundary_stopped (Reification.timedStep code oracle)
    (fun frame => OneUseSourceInterval.boundary code frame.control) fuel source.frame hBoundary, PMF.pure_map, PMF.pure_map]

theorem automaticRound_semantics (fuel : Nat) (source : Boundary State) :
    (automaticRound stateSize code oracle key keyTail fuel).semantics source =
      ((caller code oracle key keyTail fuel).semantics source).bind
        (query code oracle key keyTail).semantics :=
  round_semantics _ _ _ _ _ _ _ source

theorem automaticRound_call (fuel : Nat) (source : Boundary State) (data : CallLayout code source.frame) :
    (automaticRound stateSize code oracle key keyTail fuel).semantics source =
      PMF.pure (Boundary.mk (OneUseXorRequest.used source.spent key data.request)
        (NativeCallback.resumed data.machine.advance source.frame.state source.frame.reverseTrace data.request
          (OneUseXorRequest.reply source.spent key data.request))) := by
  rw [automaticRound_semantics, caller_at_boundary code oracle key keyTail fuel source
    (by simp [OneUseSourceInterval.boundary, data.control, data.active, data.call]), PMF.pure_bind]
  exact queryAt_semantics code oracle key keyTail source data

theorem queryAt_terminal (source : Boundary State) (hTerminal : Reification.terminal source.frame.control = true) :
    (queryAt code oracle key keyTail source).semantics () = PMF.pure source := by
  have hNo : ¬ Nonempty (CallLayout code source.frame) := by
    rintro ⟨data⟩
    simp [data.control, Reification.terminal, data.active] at hTerminal
  rw [← (queryAt code oracle key keyTail source).correct, queryAt_no_layout code oracle key keyTail source hNo,
    PMF.pure_map]

theorem automaticRound_terminal (fuel : Nat) (source : Boundary State)
    (hTerminal : Reification.terminal source.frame.control = true) :
    (automaticRound stateSize code oracle key keyTail fuel).semantics source = PMF.pure source := by
  have hb : OneUseSourceInterval.boundary code source.frame.control = true := by
    cases hc : source.frame.control <;> simp_all [Reification.terminal, OneUseSourceInterval.boundary]
  rw [automaticRound_semantics, caller_at_boundary code oracle key keyTail fuel source hb, PMF.pure_bind]
  exact queryAt_terminal code oracle key keyTail source hTerminal

/-- One ordinary native halt reaches an actual terminal before any query. -/
theorem automaticRound_halt (source : Boundary State) (machine : Machine.Configuration)
    (hControl : source.frame.control = .running machine) (hActive : machine.halted = false)
    (hHalt : code[machine.pc]? = some (.native .halt)) :
    (automaticRound stateSize code oracle key keyTail 1).semantics source =
      PMF.pure (Boundary.mk source.spent { source.frame with control := .running { machine with halted := true } }) := by
  rw [automaticRound_semantics]
  have hb : OneUseSourceInterval.boundary code source.frame.control = false := by
    simp [OneUseSourceInterval.boundary, hControl, hActive, hHalt]
  have he : Reification.timedStep code oracle source.frame =
      PMF.pure { source.frame with control := .running { machine with halted := true } } := by
    simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
      hControl, hActive, hHalt, Machine.Instruction.next]
  have hc : (caller code oracle key keyTail 1).semantics source =
      PMF.pure (Boundary.mk source.spent { source.frame with control := .running { machine with halted := true } }) := by
    change ((runToBoundary (Reification.timedStep code oracle)
      (fun frame => OneUseSourceInterval.boundary code frame.control) 1 source.frame).map Prod.fst).map _ = _
    simp [runToBoundary, hb, he, PMF.pure_map]
  rw [hc, PMF.pure_bind]
  exact queryAt_terminal code oracle key keyTail _ rfl

end CryptoOracle.Interactive.OneUseSourceRounds
