import Foundation.Crypto.Semantics.Oracle.SpentSource
import Foundation.Crypto.Semantics.Oracle.OneUseInvocation

/-! A successful handler returns to arbitrary adaptive caller execution.
The exact first-return cost is retained, and the remaining execution uses a
key-independent spent controller with the actual response and transcript. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Output : Type v} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request)
    (handler : Procedure (step native code oracle) Unit Output)
    (hEntry : handler.entry () = .handling false machine.advance state trace request
      (.preparing (.preparing (.reading key machine.outputTape {}))))
    (packet : Output → List Bool)
    (hExit : ∀ output ∈ (handler.semantics ()).support,
      handler.exit () output = .source true key (NativeCallback.resumed machine.advance state trace request (packet output)))

include hExit in
theorem adaptive_resume_law (horizon : Nat)
    (hBudget : 2 * request.length + 4 + handler.budget () ≤ horizon) :
    TimedExecution.eval (step native code oracle) horizon
      (.source false key ⟨state, .running machine, trace⟩) =
      ((invocation native code oracle false key machine state trace request before after hActive hCall hTape handler hEntry).costed ()).bind
        (fun result =>
          (TimedExecution.eval (SpentSource.step code oracle) (horizon - result.2)
            (.source (NativeCallback.resumed machine.advance state trace request (packet result.1.2)))).map (SpentSource.embed key)) := by
  let I := invocation native code oracle false key machine state trace request before after hActive hCall hTape handler hEntry
  have h := I.law () horizon (by rw [invocation_budget]; exact hBudget)
  change TimedExecution.eval _ _ (I.entry ()) = _
  rw [h]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  have hs := I.result_support () result hResult
  rw [invocation_semantics, PMF.mem_support_map_iff] at hs
  obtain ⟨output, hOutput, he⟩ := hs
  have he' : ((), output) = result.1 := he
  change TimedExecution.eval _ _ (handler.exit () result.1.2) = _
  have ho : result.1.2 = output := by rw [← he']
  rw [ho, hExit output hOutput]
  exact SpentSource.eval_embedding code oracle native key (horizon - result.2)
    (.source (NativeCallback.resumed machine.advance state trace request (packet output)))
end CryptoOracle.Interactive.OneUseSource
