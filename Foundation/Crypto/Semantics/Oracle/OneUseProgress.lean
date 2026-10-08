import Foundation.Crypto.Semantics.ProcedureProgress
import Foundation.Crypto.Semantics.Oracle.OneUseRoundSemantics

/-! Actual positive progress of call capture and certified query processing.
Ordinary intervals progress with positive fuel away from a boundary. At a
nonterminal boundary the real call layout is essential; no-layout returns
remain zero cost and are never declared terminating. -/
namespace CryptoOracle.Interactive.OneUseProgress
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u}

theorem capture (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (before after : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    Procedure.Positive (OneUseSource.capture native code oracle spent key machine state trace request
      before after hActive hCall hTape) := by
  unfold OneUseSource.capture
  apply Procedure.positive_ofFixed
  intro _
  omega

theorem invocation {Output : Type*} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (before after : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request)
    (handler : Procedure (OneUseSource.step native code oracle) Unit Output) (hEntry) :
    Procedure.Positive (OneUseSource.invocation native code oracle spent key machine state trace request
      before after hActive hCall hTape handler hEntry) := by
  unfold OneUseSource.invocation
  apply Procedure.positive_seq
  exact capture native code oracle spent key machine state trace request before after hActive hCall hTape

theorem request (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (key request : List Bool)
    (keyTail requestTail : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] requestTail request) (spent : Bool) :
    Procedure.Positive (OneUseXorRequest.invocation code oracle machine state trace key request keyTail requestTail
      hActive hCall hTape spent) := by
  cases spent <;> simp only [OneUseXorRequest.invocation, Bool.false_eq_true, ↓reduceIte]
  · split
    · apply Procedure.positive_physical
      unfold OneUseXorInvocation.invocation
      apply invocation
    · apply Procedure.positive_physical
      unfold OneUseSource.rejectedInvocation
      apply invocation
  · apply Procedure.positive_physical
    unfold OneUseSource.spentInvocation
    apply invocation

end CryptoOracle.Interactive.OneUseProgress

namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem queryAt_positive (source : Boundary State) (data : CallLayout code source.frame) :
    Procedure.Positive (queryAt code oracle key keyTail source) := by
  classical
  rw [queryAt, dif_pos (show Nonempty (CallLayout code source.frame) from ⟨data⟩)]
  apply Procedure.positive_observe
  exact OneUseProgress.request code oracle _ _ _ key _ keyTail _ _ _ _ source.spent

theorem caller_costed (fuel : Nat) (source : Boundary State) :
    (caller code oracle key keyTail fuel).costed source =
      (runToBoundary (Reification.timedStep code oracle)
        (fun frame => OneUseSourceInterval.boundary code frame.control) fuel source.frame).map
        (fun result => (Boundary.mk source.spent result.1, result.2)) := rfl

theorem caller_costed_at_boundary (fuel : Nat) (source : Boundary State)
    (hBoundary : OneUseSourceInterval.boundary code source.frame.control = true) :
    (caller code oracle key keyTail fuel).costed source = PMF.pure (source, 0) := by
  rw [caller_costed, runToBoundary_stopped (Reification.timedStep code oracle)
    (fun frame => OneUseSourceInterval.boundary code frame.control) fuel source.frame hBoundary, PMF.pure_map]

theorem round_costed (fuel : Nat) (cap : Boundary State → Nat) (hCap) (source : Boundary State) :
    (round code oracle key keyTail fuel cap hCap).costed source =
      ((caller code oracle key keyTail fuel).costed source).bind (fun first =>
        ((query code oracle key keyTail).costed first.1).map (fun second => (second.1, first.2 + second.2))) := by
  simp only [round, Procedure.observe, Procedure.seq, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The actual call layout at a nonterminal boundary, together with positive
ordinary fuel, discharges progress for a complete ordinary/query round. -/
theorem round_progress (fuel : Nat) (hFuel : 0 < fuel) (cap : Boundary State → Nat) (hCap)
    (source : Boundary State)
    (hLayout : OneUseSourceInterval.boundary code source.frame.control = true → Nonempty (CallLayout code source.frame))
    (result : Boundary State × Nat)
    (hResult : result ∈ ((round code oracle key keyTail fuel cap hCap).costed source).support) : 0 < result.2 := by
  rw [round_costed, PMF.mem_support_bind_iff] at hResult
  obtain ⟨first, hf, hs⟩ := hResult
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨second, hs, he⟩ := hs
  subst result
  cases hb : OneUseSourceInterval.boundary code source.frame.control with
  | true =>
      rw [caller_costed_at_boundary code oracle key keyTail fuel source hb, PMF.mem_support_pure_iff] at hf
      subst first
      have hp := queryAt_positive code oracle key keyTail source (Classical.choice (hLayout hb)) () second hs
      omega
  | false =>
      rw [caller_costed, PMF.mem_support_map_iff] at hf
      obtain ⟨returned, hr, he⟩ := hf
      subst first
      have hp := runToBoundary_progress (Reification.timedStep code oracle)
        (fun frame => OneUseSourceInterval.boundary code frame.control) fuel hFuel source.frame hb returned hr
      omega

end CryptoOracle.Interactive.OneUseSourceRounds
