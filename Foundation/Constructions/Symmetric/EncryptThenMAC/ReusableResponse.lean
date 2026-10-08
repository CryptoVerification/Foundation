import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffCallback
import Foundation.Crypto.Semantics.Oracle.ReusableResponseRound

/-! A repeated-request runtime for arbitrary-payload response processing.
The actual retained key enters header writing on every captured request.
Typed request validation and the handler's security semantics are separate
contracts; this controller alone does not justify reusing a one-use cipher. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

abbrev Control (State : Type u) := ReusableResponseSource.Control ResponseHandoff.Control State Tape

def begin (key : Tape) (request : List Bool) : ResponseHandoff.Control :=
  .headerWriting key request {}

noncomputable abbrev step {State : Type u} (program : Program) (code : Code) (oracle : BitOracle State) :=
  ReusableResponseSource.step (ResponseHandoffProgram.step program) begin
    ResponseHandoffProgram.Callback.ready program code oracle

variable {State : Type u} (program : Program) (code : Code) (oracle : BitOracle State)
    (key : Tape) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

theorem capture_run (before after : List (Option Bool)) (hActive : caller.halted = false)
    (hCall : code[caller.pc]? = some .call)
    (hTape : caller.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (step program code oracle) (2 * request.length + 4)
      (.source key ⟨state, .running caller, trace⟩) =
      PMF.pure (.processing caller.advance state trace request (.headerWriting key request {})) :=
  ReusableSourceRequest.capture_run (ResponseHandoffProgram.step program) begin ResponseHandoffProgram.Callback.ready
    program code oracle key caller state trace request before after hActive hCall hTape

/-- Delivery retains the exact tape layout and updated history, then the
ordinary next call begins preparation from that same private tape. -/
theorem response_as_next_request (packet : List Bool) (hActive : caller.halted = false)
    (hCall : code[caller.pc]? = some .call) :
    TimedExecution.eval (step program code oracle) (5 * packet.length + 8)
      (.calling caller state trace request (.responding (.returned packet)) key) =
      PMF.pure (.processing
        ({ caller with outputTape := ResponseLoading.loaded packet }).advance state
        ((request, packet) :: trace) packet (.headerWriting key packet {})) :=
  ReusableResponseRound.response_as_next_request (ResponseHandoffProgram.step program) begin ResponseHandoffProgram.Callback.ready
    program code oracle caller state trace request key packet hActive hCall

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse
