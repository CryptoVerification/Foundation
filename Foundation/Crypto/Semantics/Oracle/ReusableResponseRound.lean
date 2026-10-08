import Foundation.Crypto.Semantics.Oracle.ReusableSourceRequest
import Foundation.Crypto.Semantics.Oracle.ReusableResponseReturn

/-! The delivered response can determine the next real request. Both rounds
use one continuing runtime; the private store is transferred unchanged and
the transcript produced by response loading is retained. -/
namespace CryptoOracle.Interactive.ReusableResponseRound
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

/-- If the suspended caller's next instruction is a call, its newly loaded
response becomes the next request through the ordinary physical exporter.
Producing the first packet is the preceding handler's separate obligation. -/
theorem response_as_next_request (retained : Saved) (packet : List Bool)
    (hActive : saved.halted = false) (hCall : code[saved.pc]? = some .call) :
    TimedExecution.eval (ReusableResponseSource.step componentStep begin ready native code oracle)
      (5 * packet.length + 8)
      (.calling saved state trace request (.responding (.returned packet)) retained) =
      PMF.pure (.processing
        ({ saved with outputTape := ResponseLoading.loaded packet }).advance state
        ((request, packet) :: trace) packet (begin retained packet)) := by
  rw [show 5 * packet.length + 8 = (3 * packet.length + 4) + (2 * packet.length + 4) by omega,
    TimedExecution.eval_add,
    ReusableResponseReturn.packet_return componentStep begin ready native code oracle saved state trace request retained packet,
    PMF.pure_bind]
  have hc := ReusableSourceRequest.capture_run componentStep begin ready native code oracle retained
    { saved with outputTape := ResponseLoading.loaded packet } state ((request, packet) :: trace) packet [] []
    hActive hCall (by rfl)
  simpa only [NativeCallback.resumed] using hc

end CryptoOracle.Interactive.ReusableResponseRound
