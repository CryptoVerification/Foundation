import Foundation.Crypto.Semantics.Oracle.QueryMap
import Foundation.Crypto.Semantics.Oracle.Reification

/-! The native packet semantics can be used at a typed cryptographic query
interface. Encoding the typed oracle's responses and decoding native requests
does not expose hidden oracle state to the source controller. Adapter CPU costs
remain a separate obligation of the concrete reduction compiler. -/
namespace CryptoOracle.Interactive.Reification
open Foundation.Probability
universe u v s
set_option backward.isDefEq.respectTransparency false

variable {Request : Type u} {Response : Type v}

def typedPacketProgram (request : List Bool → Request) (response : Response → List Bool)
    (code : Code) (fuel : Nat) (control : Control) :
    CryptoOracle.Program Request Response (Option (List Bool)) :=
  (packetProgram code fuel control).mapQueries request response

/-- Exact joint law, including all typed requests and their encoded responses.
Malformed native requests are handled by the explicit total request decoder;
their behavior is not silently dropped from the theorem. -/
theorem typed_packet_program_run {State : Type s} (request : List Bool → Request)
    (response : Response → List Bool) (code : Code) (fuel : Nat) (control : Control)
    (oracle : Oracle Request Response State) (state : State) :
    ((typedPacketProgram request response code fuel control).run oracle state).map
        (CryptoOracle.Program.mapTranscript id response) =
      (eval code (CryptoOracle.Program.adaptOracle request response oracle)
        fuel ⟨state, control, []⟩).map
          (CryptoOracle.Program.mapTranscript request id ∘ observe packet) := by
  unfold typedPacketProgram
  rw [CryptoOracle.Program.mapQueries_run, packet_program_run, PMF.map_comp]

theorem typed_packet_program_queries (request : List Bool → Request)
    (response : Response → List Bool) (code : Code) (fuel : Nat) (control : Control) :
    (typedPacketProgram request response code fuel control).BoundedQueries fuel :=
  CryptoOracle.Program.mapQueries_queries request response (packet_program_queries code fuel control)

end CryptoOracle.Interactive.Reification
