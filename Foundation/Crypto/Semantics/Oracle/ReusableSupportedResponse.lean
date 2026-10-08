import Foundation.Crypto.Semantics.Oracle.ReusableResponseService
import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Request handlers whose physical obligations hold only on reachable
results. Certification changes proof data, never transitions or actual cost. -/
namespace CryptoOracle.Interactive.ReusableSupportedResponse
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}

structure Handler (componentStep : Component → PMF Component)
    (ready : Component → Option (Machine.Configuration × Saved)) (start : Component) where
  Output : Type x
  execution : Procedure componentStep Unit Output
  entry : execution.entry () = start
  machine : Output → Machine.Configuration
  retained : Output → Saved
  ready_exit : ∀ output ∈ (execution.semantics ()).support,
    ready (execution.exit () output) = some (machine output, retained output)
  read : Component → Output
  read_exit : ∀ output ∈ (execution.semantics ()).support, read (execution.exit () output) = output
  encode : Output → List Bool
  halt : ∀ output ∈ (execution.semantics ()).support, (machine output).halted = true
  output_tape : ∀ output ∈ (execution.semantics ()).support,
    (machine output).outputTape = Machine.ResponseExport.endTape (encode output)
  responseCap : Nat
  response_bound : ∀ output ∈ (execution.semantics ()).support, (encode output).length ≤ responseCap

namespace Handler
variable {componentStep : Component → PMF Component}
    {ready : Component → Option (Machine.Configuration × Saved)} {start : Component}
    (H : Handler.{u,w,x} componentStep ready start)

abbrev Result := {output // output ∈ (H.execution.semantics ()).support}

private noncomputable def fallback : H.Result :=
  ⟨(H.execution.semantics ()).support_nonempty.choose,
    (H.execution.semantics ()).support_nonempty.choose_spec⟩

noncomputable def totalRead (component : Component) : H.Result := by
  classical
  exact if h : H.read component ∈ (H.execution.semantics ()).support then
    ⟨H.read component, h⟩ else H.fallback

private theorem supported (argument : Unit) (output : H.Output)
    (h : output ∈ (H.execution.semantics argument).support) :
    output ∈ (H.execution.semantics ()).support := by
  cases argument
  exact h

noncomputable def supportedExecution :=
  H.execution.certify (fun output => output ∈ (H.execution.semantics ()).support) H.supported

theorem totalRead_exit (output : H.Result) : H.totalRead (H.execution.exit () output.val) = output := by
  classical
  apply Subtype.ext
  simp [totalRead, H.read_exit output.val output.property, output.property]

/-- Adapt the weaker reachable-result obligations to the existing service.
The fallback reader is proof-side totalization and is never a runtime step. -/
noncomputable def certified : ReusableResponseService.Handler componentStep ready start where
  Output := H.Result
  execution := H.supportedExecution
  entry := H.entry
  machine := fun output => H.machine output.val
  retained := fun output => H.retained output.val
  ready_exit := fun output => H.ready_exit output.val output.property
  read := H.totalRead
  read_exit := fun output => H.totalRead_exit output
  encode := fun output => H.encode output.val
  halt := fun output => H.halt output.val output.property
  output_tape := fun output => H.output_tape output.val output.property
  responseCap := H.responseCap
  response_bound := fun output _ => H.response_bound output.val output.property

theorem certified_budget : H.certified.execution.budget () = H.execution.budget () := rfl

theorem certified_semantics :
    (H.certified.execution.semantics ()).map Subtype.val = H.execution.semantics () :=
  H.execution.certify_semantics _ H.supported ()

theorem certified_costed :
    (H.certified.execution.costed ()).map (fun result => (result.1.val, result.2)) =
      H.execution.costed () := H.execution.certify_costed _ H.supported ()

end Handler

variable (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (H : Handler componentStep ready (begin retained request))

noncomputable def procedure :=
  ReusableResponseService.procedure componentStep begin ready hAbsorb native code oracle
    retained caller state trace request H.certified

theorem entry :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).entry () =
      .processing caller state trace request (begin retained request) :=
  ReusableResponseService.entry _ _ _ _ _ _ _ _ _ _ _ _ _

theorem budget :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).budget () =
      H.execution.budget () + (6 * H.responseCap + 9) := by
  rw [procedure, ReusableResponseService.budget, H.certified_budget]
  rfl

theorem semantics :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).semantics () =
      (H.execution.semantics ()).map (fun output =>
        (H.retained output, NativeCallback.resumed caller state trace request (H.encode output))) := by
  rw [procedure, ReusableResponseService.semantics]
  rw [← H.certified_semantics, PMF.map_comp]
  rfl

end CryptoOracle.Interactive.ReusableSupportedResponse
