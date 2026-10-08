import Foundation.Crypto.Semantics.Oracle.FirstAcceptance
import Foundation.Examples.OneUseInvocation
import Foundation.Examples.OneUseRejection

/-! Both outcomes of first-acceptance execution are checked against existing
whole physical executions: normal calls accept; invalid calls halt unused.
Neither test identifies budget exhaustion with a successful acceptance. -/
namespace Foundation.Examples.FirstAcceptance
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u

theorem valid_call {State : Type u} (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (input : Machine.PairPreparation.Input) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second)
    (hNext : code[machine.advance.pc]? = some (.native .halt))
    (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((CryptoOracle.Interactive.FirstAcceptance.execution
      Machine.OneTimePad.Prepared.listProcedure.code code oracle (33 * input.first.length + 34)).costed
        (.source false (Machine.PairPreparation.operand [] input.first input.firstTail)
          ⟨state, .running machine, trace⟩)).support) :
    OneUseSource.used result.1 = true := by
  apply CryptoOracle.Interactive.FirstAcceptance.completes _ _ _ _ _ _ _ h
  rw [OneUseInvocationExamples.run code oracle machine state trace input hActive hCall hTape hNext]
  intro finish hf
  rw [PMF.mem_support_pure_iff] at hf
  subst finish
  rfl

theorem invalid_call {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (sourceInput : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))
    (input : Machine.PreparationCheck.FailureInput) (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((CryptoOracle.Interactive.FirstAcceptance.execution native
      OneUseRejectionExamples.code oracle (12 * Machine.PreparationCheck.consumed input + 26)).costed
        (.handling false (OneUseRejectionExamples.saved sourceInput input) state trace input.second
          (.preparing (.preparing (.reading
            (Machine.PairPreparation.operand [] input.first input.firstTail)
            (Machine.PairPreparation.operand [] input.second input.secondTail) {}))))).support) :
    OneUseSource.used result.1 = false ∧ result.2 = 12 * Machine.PreparationCheck.consumed input + 26 := by
  exact CryptoOracle.Interactive.FirstAcceptance.exhausted_when_unused _ _ _ _ _
    (OneUseRejectionExamples.unused_after_stop native oracle sourceInput state trace input) result h

end Foundation.Examples.FirstAcceptance
