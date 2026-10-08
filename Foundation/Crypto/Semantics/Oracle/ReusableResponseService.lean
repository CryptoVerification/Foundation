import Foundation.Crypto.Semantics.Oracle.ReusableSourceRound
import Foundation.Crypto.Semantics.Oracle.ReusableResponseInvocation

/-! Package a component execution proof as a callable service returning the
entire saved private value and resumed public caller. Neither the package nor
its logical observation introduces a runtime instruction. -/
namespace CryptoOracle.Interactive.ReusableResponseService
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
  ready_exit : ∀ output, ready (execution.exit () output) = some (machine output, retained output)
  read : Component → Output
  read_exit : ∀ output, read (execution.exit () output) = output
  encode : Output → List Bool
  halt : ∀ output, (machine output).halted = true
  output_tape : ∀ output, (machine output).outputTape = Machine.ResponseExport.endTape (encode output)
  responseCap : Nat
  response_bound : ∀ output ∈ (execution.semantics ()).support, (encode output).length ≤ responseCap

variable (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (H : Handler componentStep ready (begin retained request))

noncomputable def invocation :=
  ReusableResponseInvocation.whole componentStep begin ready native code oracle caller state trace request
    H.execution H.machine H.retained H.ready_exit hAbsorb H.read H.read_exit
    H.encode H.halt H.output_tape H.responseCap H.response_bound

noncomputable def procedure :=
  (invocation componentStep begin ready hAbsorb native code oracle retained caller state trace request H).observe
    (fun result => (H.retained result.1.1, NativeCallback.resumed caller state trace request result.2.1))
    (fun _ output => ReusableSourceRound.embed output)
    (fun _ _ _ => rfl)

theorem entry :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).entry () =
      .processing caller state trace request (begin retained request) := by
  change ReusableResponseSource.Control.processing caller state trace request (H.execution.entry ()) = _
  rw [H.entry]

theorem exit (output : ReusableSourceRound.Source (State := State) (Saved := Saved)) :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).exit () output =
      ReusableSourceRound.embed output := rfl

theorem budget :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).budget () =
      H.execution.budget () + (6 * H.responseCap + 9) := by
  change (invocation componentStep begin ready hAbsorb native code oracle retained caller state trace request H).budget () = _
  exact ReusableResponseInvocation.budget componentStep begin ready native code oracle caller state trace request
    H.execution H.machine H.retained H.ready_exit hAbsorb H.read H.read_exit
    H.encode H.halt H.output_tape H.responseCap H.response_bound

theorem semantics :
    (procedure componentStep begin ready hAbsorb native code oracle retained caller state trace request H).semantics () =
      (H.execution.semantics ()).map (fun output =>
        (H.retained output, NativeCallback.resumed caller state trace request (H.encode output))) := by
  change ((invocation componentStep begin ready hAbsorb native code oracle retained caller state trace request H).semantics ()).map _ = _
  rw [invocation, ReusableResponseInvocation.semantics, PMF.map_comp]
  rfl

end CryptoOracle.Interactive.ReusableResponseService
