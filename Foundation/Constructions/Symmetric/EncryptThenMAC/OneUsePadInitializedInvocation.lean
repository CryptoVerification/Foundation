import Foundation.Constructions.Symmetric.EncryptThenMAC.OneUsePadInvocation
import Foundation.Crypto.Semantics.Oracle.OneUseBitInitialization
import Foundation.Crypto.Semantics.Oracle.InitializationContinuation
import Foundation.Crypto.Semantics.Oracle.ControllerResourceEnvelope
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! The typed arbitrary-width pad call is connected to actual native key
generation by the same generic initialization/continuation rule. The caller
starts at an existing real call instruction with its plaintext request tape.
Post-return source execution remains in the same charged residual machine. -/
namespace Foundation.Symmetric.EncryptThenMAC.OneUsePadInitializedInvocation
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    {length : Nat} (message : Bits length)
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = OneUsePadInvocation.requestTape message)

def caller : Configuration State := ⟨state, .running machine, trace⟩

noncomputable def continuation :
    Procedure (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      (Bits length) (OneUseSource.Control State) :=
  Procedure.dispatch (fun key : Bits length =>
    OneUsePadInvocation.invocation code oracle machine state trace key message hActive hCall hTape false)

noncomputable def complete :=
  OneUseInitialization.follow Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
    code oracle (caller machine state trace)
    (OneUseBitInitialization.initialization Machine.OneTimePad.Prepared.listProcedure.code code oracle
      (caller machine state trace) length)
    (fun key : Bits length => OneUsePadInvocation.keyStore key)
    (fun _ _ _ => rfl)
    (continuation code oracle machine state trace message hActive hCall hTape)
    (fun key => OneUsePadInvocation.entry code oracle machine state trace key message hActive hCall hTape false)
    (fun _ => 33 * length + 33)
    (fun _ result _ => le_of_eq
      (OneUsePadInvocation.budget code oracle machine state trace result.1 message hActive hCall hTape false))

theorem budget :
    (complete code oracle machine state trace message hActive hCall hTape).budget () = 39 * length + 38 := by
  unfold complete
  rw [OneUseInitialization.follow_budget, OneUseBitInitialization.budget]
  omega

/-- This is the logical return distribution of the certified real execution;
its full joint cost law additionally records any generation-time correlation. -/
theorem semantics :
    (complete code oracle machine state trace message hActive hCall hTape).semantics () =
      (uniform (Bits length)).map (fun key =>
        ((key, ()), OneUsePadInvocation.result machine state trace key message false)) := by
  unfold complete
  rw [OneUseInitialization.follow_semantics]
  simp only [continuation, Procedure.dispatch]
  simp_rw [OneUsePadInvocation.semantics]
  simp only [OneUseBitInitialization.initialization, OneUseInitialization.semantics,
    Machine.PrivateBitGeneration.native, Machine.Procedure.ofFixed, TimedExecution.Procedure.ofFixed,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def]
  rfl

/-- The same runtime continues after the actual initialization and call costs;
the source is neither frozen at return nor restarted in a separate VM. -/
theorem resume (horizon : Nat) (hBudget : 39 * length + 38 ≤ horizon) :
    TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
        code oracle (caller machine state trace)) horizon
      (.initializing (.generating (Machine.Configuration.initial (List.replicate length true)))) =
      ((complete code oracle machine state trace message hActive hCall hTape).costed ()).bind
        (fun returned => TimedExecution.eval
          (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
            code oracle (caller machine state trace)) (horizon - returned.2)
          (.active returned.1.2)) := by
  have h := (complete code oracle machine state trace message hActive hCall hTape).law
    () horizon (by rw [budget]; exact hBudget)
  change TimedExecution.eval _ _ ((complete code oracle machine state trace message hActive hCall hTape).entry ()) = _
  convert h using 1
  simp only [complete, OneUseInitialization.follow, Procedure.seq, Procedure.reindex,
    Procedure.transport, continuation, Procedure.dispatch, OneUsePadInvocation.invocation,
    Bool.false_eq_true, ↓reduceIte, Procedure.physical]


/-- The whole native generation/call interval is covered at every prefix.
Initial caller tapes and prior history are counted explicitly in the extent. -/
theorem memory_peak (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ 39 * length + 38)
    (target : OneUseInitialization.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
        code oracle (caller machine state trace)) elapsed
      (.initializing (.generating (Machine.Configuration.initial (List.replicate length true))))).support) :
    ControllerStorage.initializationCells stateSize (caller machine state trace) target ≤
      4 * (ControllerExtent.initializationExtent stateSize (caller machine state trace)
        (.initializing (.generating (Machine.Configuration.initial (List.replicate length true)))) +
          (39 * length + 38) * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.initializationExtent stateSize (caller machine state trace)
        (.initializing (.generating (Machine.Configuration.initial (List.replicate length true)))) +
          (39 * length + 38) * (stateIncrement + responseCap + 2)) + 2 :=
  ControllerExtent.initialization_peak stateSize Machine.OneTimePad.keygen
    Machine.OneTimePad.Prepared.listProcedure.code code oracle (caller machine state trace)
    stateIncrement responseCap hOracle (39 * length + 38) elapsed hElapsed
    (.initializing (.generating (Machine.Configuration.initial (List.replicate length true)))) target h

end Foundation.Symmetric.EncryptThenMAC.OneUsePadInitializedInvocation
