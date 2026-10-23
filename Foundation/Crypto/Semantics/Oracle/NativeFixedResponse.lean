import Foundation.Crypto.Semantics.Oracle.QueryTransfer
import Foundation.Crypto.Semantics.Probability.Facts

/-! Exact continuing-call law for an oracle with fixed response width.
The time includes call capture, request export, capability invocation,
cell-level response loading and rewind. The source code, input/work tape,
oracle state and previous transcript are retained. Oracle-internal work is
still a separate service obligation, not hidden inside this caller bound.
-/
namespace CryptoOracle.Interactive.QueryTransfer
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
universe u

theorem fixed_response_call {State : Type u} (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (active : machine.halted = false)
    (call : code[machine.pc]? = some .call)
    (packet : machine.outputTape = RequestExport.packetTape before after request)
    (width : Nat) (response : ∀ answer ∈ (oracle state request).support, answer.2.length = width) :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 3 * width + 6)
        (⟨state, .running machine, trace⟩ : Configuration State) =
      (oracle state request).map (resumed machine.advance trace request) := by
  let stage := fullStage code oracle machine state trace request before after active call packet width
    (fun answer reachable => le_of_eq (response answer reachable))
  have law := stage.law (2 * request.length + 3 * width + 6) (by
    change (2 * request.length + 3) + (3 * width + 3) ≤ _
    omega)
  simp only [id_eq] at law
  rw [law]
  simp only [stage, fullStage, QueryTransfer.stage, PMF.bind_map, Function.comp_def]
  change ((oracle state request).bind fun answer =>
    TimedExecution.eval (Reification.timedStep code oracle)
      (2 * request.length + 3 * width + 6 - (2 * request.length + 3 + (3 * answer.2.length + 3)))
      (resumed machine.advance trace request answer)) = _
  rw [PMF.map]
  apply bind_congr_of_support
  intro answer reachable
  rw [response answer reachable]
  have unused : 2 * request.length + 3 * width + 6 - (2 * request.length + 3 + (3 * width + 3)) = 0 := by omega
  rw [unused]
  rfl

end CryptoOracle.Interactive.QueryTransfer
