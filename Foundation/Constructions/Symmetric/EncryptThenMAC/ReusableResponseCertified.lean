import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponse
import Foundation.Crypto.Semantics.Oracle.ReusableResponseInvocation
import Foundation.Crypto.Semantics.Oracle.ReusableResponseService

/-! Complete arbitrary-payload response preparation, certified native
handling and caller resumption in the reusable request runtime. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Certified
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type v} (program : Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

abbrev Result (Output : Type u) := ((Unit × Unit) × Unit) × Output

variable {Output : Type u} (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload)
    (read : Machine.Configuration → Output)
    (hRead : ∀ output, read (handler.exit () output) = output)
    (encode : Output → List Bool)
    (hHalt : ∀ output, (handler.exit () output).halted = true)
    (hTape : ∀ output, (handler.exit () output).outputTape = ResponseExport.endTape (encode output))

private def reader : ResponseHandoff.Control → Result Output
  | .authenticating _ machine => ((((), ()), ()), read machine)
  | _ => ((((), ()), ()), read (preparedMachine key payload))

include hRead in
private theorem reader_exit (result : Result Output) :
    reader key payload read ((Repeated.complete program key payload handler hEntry).exit () result) = result := by
  rcases result with ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, output⟩
  change ((((), ()), ()), read (handler.exit () output)) = _
  rw [hRead]

include hHalt in
private theorem ready_exit (result : Result Output) :
    ResponseHandoffProgram.Callback.ready ((Repeated.complete program key payload handler hEntry).exit () result) =
      some (handler.exit () result.2, retainedKey key) := by
  rcases result with ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, output⟩
  simp [Repeated.complete_exit, ResponseHandoffProgram.Callback.ready, hHalt]

variable (cap : Nat) (hCap : ∀ output ∈ (handler.semantics ()).support, (encode output).length ≤ cap)

include hCap in
private theorem result_cap (result : Result Output)
    (h : result ∈ ((Repeated.complete program key payload handler hEntry).semantics ()).support) :
    (encode result.2).length ≤ cap := by
  rw [Repeated.complete_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact hCap output ho

/-- The same concrete preparation/handler proof can be supplied to the
common source-round interface. Its entry is the actual restored key tape;
no request or private tape is replaced by a semantic surrogate. -/
noncomputable def handlerCertificate :
    ReusableResponseService.Handler (ResponseHandoffProgram.step program)
      ResponseHandoffProgram.Callback.ready (ReusableResponse.begin (retainedKey key) payload) where
  Output := Result Output
  execution := Repeated.complete program key payload handler hEntry
  entry := rfl
  machine := fun result => handler.exit () result.2
  retained := fun _ => retainedKey key
  ready_exit := ready_exit program key payload handler hEntry hHalt
  read := reader key payload read
  read_exit := reader_exit program key payload handler hEntry read hRead
  encode := fun result => encode result.2
  halt := fun result => hHalt result.2
  output_tape := fun result => hTape result.2
  responseCap := cap
  response_bound := result_cap program key payload handler hEntry encode cap hCap

noncomputable def sourceService :=
  ReusableResponseService.procedure (ResponseHandoffProgram.step program) ReusableResponse.begin
    ResponseHandoffProgram.Callback.ready (ResponseHandoffProgram.Callback.ready_absorb program)
    program code oracle (retainedKey key) caller state trace payload
    (handlerCertificate program key payload handler hEntry read hRead encode hHalt hTape cap hCap)

theorem sourceService_entry :
    (sourceService program code oracle caller state trace key payload handler hEntry read hRead encode hHalt hTape cap hCap).entry () =
      .processing caller state trace payload (.headerWriting (retainedKey key) payload {}) :=
  ReusableResponseService.entry _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sourceService_budget :
    (sourceService program code oracle caller state trace key payload handler hEntry read hRead encode hHalt hTape cap hCap).budget () =
      9 * key.length + 3 * payload.length + handler.budget () + 6 * cap + 17 := by
  rw [sourceService, ReusableResponseService.budget]
  change (Repeated.complete program key payload handler hEntry).budget () + (6 * cap + 9) = _
  rw [Repeated.complete_budget]
  omega

theorem sourceService_semantics :
    (sourceService program code oracle caller state trace key payload handler hEntry read hRead encode hHalt hTape cap hCap).semantics () =
      (handler.semantics ()).map (fun output =>
        (retainedKey key, NativeCallback.resumed caller state trace payload (encode output))) := by
  rw [sourceService, ReusableResponseService.semantics]
  change ((Repeated.complete program key payload handler hEntry).semantics ()).map _ = _
  rw [Repeated.complete_semantics, PMF.map_comp]
  rfl

noncomputable def whole :=
  ReusableResponseInvocation.whole
    (ResponseHandoffProgram.step program) ReusableResponse.begin ResponseHandoffProgram.Callback.ready program code oracle caller state trace request
    (Repeated.complete program key payload handler hEntry)
    (fun result : Result Output => handler.exit () result.2) (fun _ => retainedKey key)
    (ready_exit program key payload handler hEntry hHalt) (ResponseHandoffProgram.Callback.ready_absorb program)
    (reader key payload read) (reader_exit program key payload handler hEntry read hRead)
    (fun result : Result Output => encode result.2)
    (fun result => hHalt result.2) (fun result => hTape result.2)
    cap (result_cap program key payload handler hEntry encode cap hCap)

theorem budget :
    (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).budget () =
      9 * key.length + 3 * payload.length + handler.budget () + 6 * cap + 17 := by
  rw [whole, ReusableResponseInvocation.budget, Repeated.complete_budget]
  omega

theorem entry :
    (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).entry () =
      .processing caller state trace request (.headerWriting (retainedKey key) payload {}) := rfl

theorem semantics :
    (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).semantics () =
      (handler.semantics ()).map (fun output => ((((((), ()), ()), output), ()), (encode output, ()))) := by
  rw [whole, ReusableResponseInvocation.semantics, Repeated.complete_semantics, PMF.map_comp]
  rfl

/-- This is the endpoint distribution, not a fixed-horizon claim that
freezes the resumed caller. The costed procedure supplies that residual law. -/
theorem distribution :
    ((whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).costed ()).map
      (fun result => (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).exit () result.1) =
      (handler.semantics ()).map (fun output => ReusableResponseSource.Control.source (retainedKey key)
        (NativeCallback.resumed caller state trace request (encode output))) := by
  rw [whole, ReusableResponseInvocation.distribution, Repeated.complete_semantics, PMF.map_comp]
  rfl

theorem law (horizon : Nat)
    (hBudget : 9 * key.length + 3 * payload.length + handler.budget () + 6 * cap + 17 ≤ horizon) :
    TimedExecution.eval (ReusableResponse.step program code oracle) horizon
      (.processing caller state trace request (.headerWriting (retainedKey key) payload {})) =
      ((whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).costed ()).bind
        (fun result => TimedExecution.eval (ReusableResponse.step program code oracle)
          (horizon - result.2) (.source (retainedKey key)
            (NativeCallback.resumed caller state trace request result.1.2.1))) := by
  exact (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).law
    () horizon (by rw [budget]; exact hBudget)

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Certified
