import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffRepeated
import Foundation.Crypto.Semantics.Oracle.ComponentResponseCallback

/-! A single transition system for retained-key response preparation,
certified native handling, charged export ownership transfer, physical
response delivery and continuing source execution. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u v
set_option backward.isDefEq.respectTransparency false

/-- Readiness inspects only the control tag and native halt bit; both the
native machine and key are passed through without tape reconstruction. -/
def ready : ResponseHandoff.Control → Option (Machine.Configuration × Tape)
  | .authenticating key machine => if machine.halted then some (machine, key) else none
  | _ => none

theorem ready_absorb (program : Program) (component : ResponseHandoff.Control)
    (h : ComponentResponseCallback.componentBoundary ready component = true) :
    ResponseHandoffProgram.step program component = PMF.pure component := by
  cases component <;> simp only [ComponentResponseCallback.componentBoundary, ready] at h
  all_goals try contradiction
  rename_i key machine
  by_cases hh : machine.halted = true
  · simp [ResponseHandoffProgram.step, stepPMF, next, hh, PMF.pure_map]
  · simp [hh] at h

variable {State : Type v} (program : Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable abbrev step := ComponentResponseCallback.step
  (ResponseHandoffProgram.step program) ready program code oracle caller state trace request

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
    ready ((Repeated.complete program key payload handler hEntry).exit () result) =
      some (handler.exit () result.2, retainedKey key) := by
  rcases result with ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, output⟩
  simp [Repeated.complete_exit, ready, hHalt]

variable (cap : Nat) (hCap : ∀ output ∈ (handler.semantics ()).support, (encode output).length ≤ cap)

include hCap in
private theorem result_cap (result : Result Output)
    (h : result ∈ ((Repeated.complete program key payload handler hEntry).semantics ()).support) :
    (encode result.2).length ≤ cap := by
  rw [Repeated.complete_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact hCap output ho

noncomputable def whole :=
  ComponentResponseCallback.whole
    (ResponseHandoffProgram.step program) ready program code oracle caller state trace request
    (Repeated.complete program key payload handler hEntry)
    (fun result : Result Output => handler.exit () result.2) (fun _ => retainedKey key)
    (ready_exit program key payload handler hEntry hHalt) (ready_absorb program)
    (reader key payload read) (reader_exit program key payload handler hEntry read hRead)
    (fun result : Result Output => encode result.2)
    (fun result => hHalt result.2) (fun result => hTape result.2)
    cap (result_cap program key payload handler hEntry encode cap hCap)

theorem budget :
    (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).budget () =
      9 * key.length + 3 * payload.length + handler.budget () + 6 * cap + 16 := by
  rw [whole, ComponentResponseCallback.whole_budget, Repeated.complete_budget]
  omega

theorem entry :
    (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).entry () =
      .processing (.headerWriting (retainedKey key) payload {}) := rfl

/-- This is the endpoint distribution, not a fixed-horizon claim that
freezes the resumed caller. The costed procedure supplies that residual law. -/
theorem distribution :
    ((whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).costed ()).map
      (fun result => (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).exit () result.1) =
      (handler.semantics ()).map (fun output => ComponentResponseCallback.Control.delivering
        (.source (NativeCallback.resumed caller state trace request (encode output)), retainedKey key)) := by
  rw [whole, ComponentResponseCallback.whole_distribution, Repeated.complete_semantics, PMF.map_comp]
  rfl

theorem law (horizon : Nat)
    (hBudget : 9 * key.length + 3 * payload.length + handler.budget () + 6 * cap + 16 ≤ horizon) :
    TimedExecution.eval (step program code oracle caller state trace request) horizon
      (.processing (.headerWriting (retainedKey key) payload {})) =
      ((whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).costed ()).bind
        (fun result => TimedExecution.eval (step program code oracle caller state trace request)
          (horizon - result.2) (.delivering
            (.source (NativeCallback.resumed caller state trace request result.1.2.2.1), retainedKey key))) := by
  exact (whole program code oracle caller state trace request key payload handler hEntry read hRead encode hHalt hTape cap hCap).law
    () horizon (by rw [budget]; exact hBudget)

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback
