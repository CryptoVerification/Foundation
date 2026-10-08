import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponse
import Foundation.Crypto.Semantics.Oracle.ReusableSupportedResponse
import Foundation.Crypto.Semantics.Machine.ProcedureModel

/-! Connect arbitrary typed native models to actual retained-key request
preparation and response delivery. The mathematical result need not be
recoverable from public bytes: the complete physical exit is the service's
internal result. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Model
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {State : Type w}
    (M : Machine.ProcedureModel Input Output) (input : Input) (key payload : List Bool)
    (hEntry : M.procedure.execution.entry input = preparedMachine key payload)

abbrev Result := ((Unit × Unit) × Unit) × Machine.Configuration

noncomputable def component :=
  Repeated.complete M.procedure.code key payload (M.completion input).execution hEntry

theorem component_exit (result : Result) :
    (component M input key payload hEntry).exit () result =
      .authenticating (retainedKey key) result.2 := by
  rcases result with ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, machine⟩
  rfl

theorem component_semantics :
    (component M input key payload hEntry).semantics () =
      (M.ideal input).map (fun output => ((((), ()), ()), M.procedure.execution.exit input output)) := by
  rw [component, Repeated.complete_semantics, M.completion_semantics, PMF.map_comp]
  rfl

private def read (c : ResponseHandoff.Control) : Result :=
  match c with
  | .authenticating _ machine => ((((), ()), ()), machine)
  | _ => ((((), ()), ()), preparedMachine key payload)

private theorem read_exit (result : Result) :
    read key payload ((component M input key payload hEntry).exit () result) = result := by
  rw [component_exit]
  rcases result with ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, machine⟩
  rfl

private theorem result_halt (result : Result)
    (h : result ∈ ((component M input key payload hEntry).semantics ()).support) :
    result.2.halted = true := by
  rw [component_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact M.halt input output ho

variable
    (hTape : ∀ output ∈ (M.ideal input).support,
      (M.procedure.execution.exit input output).outputTape = ResponseExport.endTape (M.encode input output))
    (cap : Nat) (hCap : ∀ output ∈ (M.ideal input).support, (M.encode input output).length ≤ cap)

include hTape in
private theorem result_tape (result : Result)
    (h : result ∈ ((component M input key payload hEntry).semantics ()).support) :
    result.2.outputTape = ResponseExport.endTape result.2.outputBits := by
  rw [component_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  rw [M.output input output ho]
  exact hTape output ho

include hCap in
private theorem result_cap (result : Result)
    (h : result ∈ ((component M input key payload hEntry).semantics ()).support) :
    result.2.outputBits.length ≤ cap := by
  rw [component_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  rw [M.output input output ho]
  exact hCap output ho

noncomputable def handler :
    ReusableSupportedResponse.Handler (ResponseHandoffProgram.step M.procedure.code)
      Callback.ready (ReusableResponse.begin (retainedKey key) payload) where
  Output := Result
  execution := component M input key payload hEntry
  entry := rfl
  machine := Prod.snd
  retained := fun _ => retainedKey key
  ready_exit := by
    intro result hr
    rw [component_exit]
    simp [Callback.ready, result_halt M input key payload hEntry result hr]
  read := read key payload
  read_exit := fun result _ => read_exit M input key payload hEntry result
  encode := fun result => result.2.outputBits
  halt := result_halt M input key payload hEntry
  output_tape := result_tape M input key payload hEntry hTape
  responseCap := cap
  response_bound := result_cap M input key payload hEntry cap hCap

variable (code : Code) (oracle : BitOracle State) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool))

noncomputable def service :=
  ReusableSupportedResponse.procedure (ResponseHandoffProgram.step M.procedure.code)
    ReusableResponse.begin Callback.ready (Callback.ready_absorb M.procedure.code)
    M.procedure.code code oracle (retainedKey key) caller state trace payload
    (handler M input key payload hEntry hTape cap hCap)

theorem entry :
    (service M input key payload hEntry hTape cap hCap code oracle caller state trace).entry () =
      .processing caller state trace payload (.headerWriting (retainedKey key) payload {}) :=
  ReusableSupportedResponse.entry _ _ _ _ _ _ _ _ _ _ _ _ _

theorem budget :
    (service M input key payload hEntry hTape cap hCap code oracle caller state trace).budget () =
      9 * key.length + 3 * payload.length + M.procedure.execution.budget input + 6 * cap + 17 := by
  rw [service, ReusableSupportedResponse.budget]
  change (component M input key payload hEntry).budget () + (6 * cap + 9) = _
  rw [component, Repeated.complete_budget, M.completion_budget]
  omega

theorem exit (result : Tape × CryptoOracle.Interactive.Configuration State) :
    (service M input key payload hEntry hTape cap hCap code oracle caller state trace).exit () result =
      ReusableResponseSource.Control.source result.1 result.2 := rfl

/-- The continuing caller is evaluated for its real remaining time. It is
not frozen at the response boundary, even if another request follows. -/
theorem law (horizon : Nat)
    (hBudget : 9 * key.length + 3 * payload.length + M.procedure.execution.budget input +
      6 * cap + 17 ≤ horizon) :
    TimedExecution.eval (ReusableResponse.step M.procedure.code code oracle) horizon
      (.processing caller state trace payload (.headerWriting (retainedKey key) payload {})) =
      ((service M input key payload hEntry hTape cap hCap code oracle caller state trace).costed ()).bind
        (fun result => TimedExecution.eval (ReusableResponse.step M.procedure.code code oracle)
          (horizon - result.2) (.source result.1.1 result.1.2)) := by
  have h := (service M input key payload hEntry hTape cap hCap code oracle caller state trace).law
    () horizon (by rw [budget]; exact hBudget)
  rw [entry] at h
  exact h

theorem budget_polynomial {keyLength payloadLength handlerBudget responseCap : Nat → Nat}
    (hKey : PolynomiallyBounded keyLength) (hPayload : PolynomiallyBounded payloadLength)
    (hHandler : PolynomiallyBounded handlerBudget) (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n =>
      9 * keyLength n + 3 * payloadLength n + handlerBudget n + 6 * responseCap n + 17) :=
  (((((PolynomiallyBounded.const 9).mul hKey).add ((PolynomiallyBounded.const 3).mul hPayload)).add
    hHandler).add ((PolynomiallyBounded.const 6).mul hResponse)).add (PolynomiallyBounded.const 17)

/-- The real request is delivered with the model's bytes. The saved key
tape and complete resumed caller are retained by the actual service. -/
theorem semantics :
    (service M input key payload hEntry hTape cap hCap code oracle caller state trace).semantics () =
      (M.ideal input).map (fun output =>
        (retainedKey key, NativeCallback.resumed caller state trace payload (M.encode input output))) := by
  rw [service, ReusableSupportedResponse.semantics]
  change ((component M input key payload hEntry).semantics ()).map _ = _
  rw [component_semantics, PMF.map_comp]
  simp only [PMF.map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext output ho
  change PMF.pure (retainedKey key, NativeCallback.resumed caller state trace payload
    (M.procedure.execution.exit input output).outputBits) = _
  rw [M.output input output ho]
  rfl

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Model
