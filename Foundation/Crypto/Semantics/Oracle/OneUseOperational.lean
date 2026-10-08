import Foundation.Crypto.Semantics.ProcedureBoundaryReachability
import Foundation.Crypto.Semantics.Oracle.OneUseRoundSemantics

/-! Operational reachability of actual request capture, native response,
rejection and the ordinary/query round. Costs retain the original caller's
full physical state and are not replaced by the declared round caps. -/
namespace CryptoOracle.Interactive.OneUseOperational
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u}

theorem delivery (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (first second : Machine.Tape) :
    Procedure.Operational (OneUseDelivery.packetDelivery native code oracle spent saved state trace request first second) := by
  unfold OneUseDelivery.packetDelivery OneUseDelivery.packetBody OneUseDelivery.reply
  apply Procedure.operational_seq
  · apply Procedure.operational_reindex
    apply Procedure.operational_liftBoundary
  · apply Procedure.operational_ofFixed

theorem rejection (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (input : Machine.PreparationCheck.FailureInput) :
    Procedure.Operational (OneUseRejection.whole native code oracle saved state trace request input) := by
  unfold OneUseRejection.whole OneUseRejection.preparation OneUseRejection.handoff
  apply Procedure.operational_seq
  · apply Procedure.operational_seq
    · apply Procedure.operational_liftBoundary
    · apply Procedure.operational_ofFixed
  · apply Procedure.operational_reindex
    exact delivery native code oracle false saved state trace request _ _

theorem preparedResponse {Input : Type v} {Output : Type w}
    (code : Code) (oracle : BitOracle State) (saved : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (physical : Machine.PairPreparation.Input) (input : Input)
    (hEntry : P.execution.entry input = { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave physical.first physical.second).map some ++ [none]) }) :
    Procedure.Operational (OneUseSource.preparedResponse code oracle saved state trace request
      P encode hHalt hTape read hRead cap hCap physical input hEntry) := by
  unfold OneUseSource.preparedResponse
  apply Procedure.operational_seq
  · apply Procedure.operational_reindex
    unfold OneUseSource.preparationPrefix OneUseSource.preparation OneUseSource.acceptance
    apply Procedure.operational_seq
    · apply Procedure.operational_remember
      apply Procedure.operational_liftBoundary
    · apply Procedure.operational_ofFixed
  · apply Procedure.operational_reindex
    unfold OneUseSource.nativeResponse
    apply Procedure.operational_seq
    · apply Procedure.operational_seq
      · apply Procedure.operational_remember
        unfold OneUseSource.rawBody
        apply Procedure.operational_reindex
        apply Procedure.operational_liftBoundary
      · unfold OneUseSource.rawHandoff
        apply Procedure.operational_ofFixed
    · apply Procedure.operational_reindex
      unfold OneUseSource.tagged
      apply Procedure.operational_seq
      · apply Procedure.operational_seq
        · apply Procedure.operational_remember
          unfold OneUseSource.tagWriting
          apply Procedure.operational_reindex
          apply Procedure.operational_liftBoundary
        · unfold OneUseSource.tagHandoff
          apply Procedure.operational_ofFixed
      · apply Procedure.operational_reindex
        exact delivery _ code oracle true saved state trace request _ _

theorem xorResponse (code : Code) (oracle : BitOracle State) (saved : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)
    (input : Machine.PairPreparation.Input) :
    Procedure.Operational (OneUseXorResponse.response code oracle saved state trace request input) := by
  unfold OneUseXorResponse.response
  apply preparedResponse

theorem capture (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (before after : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    Procedure.Operational (OneUseSource.capture native code oracle spent key machine state trace request
      before after hActive hCall hTape) := by
  unfold OneUseSource.capture
  apply Procedure.operational_ofFixed

theorem invocation {Output : Type*} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (before after : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request)
    (handler : Procedure (OneUseSource.step native code oracle) Unit Output)
    (hEntry) (hHandler : Procedure.Operational handler) :
    Procedure.Operational (OneUseSource.invocation native code oracle spent key machine state trace request
      before after hActive hCall hTape handler hEntry) := by
  unfold OneUseSource.invocation
  apply Procedure.operational_seq
  · exact capture native code oracle spent key machine state trace request before after hActive hCall hTape
  · exact Procedure.operational_reindex handler hHandler _

theorem request (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (key request : List Bool)
    (keyTail requestTail : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] requestTail request) (spent : Bool) :
    Procedure.Operational (OneUseXorRequest.invocation code oracle machine state trace key request keyTail requestTail
      hActive hCall hTape spent) := by
  cases spent <;> simp only [OneUseXorRequest.invocation, Bool.false_eq_true, ↓reduceIte]
  · split
    · apply Procedure.operational_physical
      unfold OneUseXorInvocation.invocation
      apply invocation
      exact xorResponse code oracle machine.advance state trace request _
    · apply Procedure.operational_physical
      unfold OneUseSource.rejectedInvocation
      apply invocation
      exact rejection _ code oracle machine.advance state trace request _
  · apply Procedure.operational_physical
    unfold OneUseSource.spentInvocation
    apply invocation
    unfold OneUseSource.spentRejection
    apply Procedure.operational_ofFixed

end CryptoOracle.Interactive.OneUseOperational

namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem queryAt_operational (source : Boundary State) : Procedure.Operational (queryAt code oracle key keyTail source) := by
  classical
  unfold queryAt
  split
  · apply Procedure.operational_observe
    exact OneUseOperational.request code oracle _ _ _ key _ keyTail _ _ _ _ source.spent
  · apply Procedure.operational_ofFixed

theorem callerAt_operational (fuel : Nat) (source : Boundary State) :
    Procedure.Operational (callerAt code oracle key keyTail fuel source) := by
  unfold callerAt
  apply Procedure.operational_observe
  apply Procedure.operational_reindex
  unfold OneUseSourceInterval.interval
  apply Procedure.operational_interval

theorem round_operational (fuel : Nat) (cap : Boundary State → Nat) (hCap) :
    Procedure.Operational (round code oracle key keyTail fuel cap hCap) := by
  unfold round
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · exact Procedure.operational_dispatch _ (callerAt_operational code oracle key keyTail fuel)
  · exact Procedure.operational_dispatch _ (queryAt_operational code oracle key keyTail)

theorem automaticRound_operational (stateSize : State → Nat) (fuel : Nat) :
    Procedure.Operational (automaticRound stateSize code oracle key keyTail fuel) :=
  round_operational code oracle key keyTail fuel _ _

end CryptoOracle.Interactive.OneUseSourceRounds
