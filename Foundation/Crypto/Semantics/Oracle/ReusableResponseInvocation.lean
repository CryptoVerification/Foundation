import Foundation.Crypto.Semantics.Oracle.ReusableResponseComponent
import Foundation.Crypto.Semantics.Oracle.ReusableResponseDelivery
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Complete certified request processing in the reusable runtime. The next
request is serviced by the same continuing step relation after resumption. -/
namespace CryptoOracle.Interactive.ReusableResponseInvocation
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w} {Output : Type x}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (P : Procedure componentStep Unit Output)
    (machine : Output → Machine.Configuration) (retained : Output → Saved)
    (hReady : ∀ output, ready (P.exit () output) = some (machine output, retained output))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (read : Component → Output) (hRead : ∀ output, read (P.exit () output) = output)
    (encode : Output → List Bool)
    (hHalt : ∀ output, (machine output).halted = true)
    (hTape : ∀ output, (machine output).outputTape = Machine.ResponseExport.endTape (encode output))
    (cap : Nat) (hCap : ∀ output ∈ (P.semantics ()).support, (encode output).length ≤ cap)

def input (output : Output) : RetainedResponseDelivery.Input :=
  ⟨machine output, encode output, hHalt output, hTape output⟩

noncomputable def delivery :=
  Procedure.dispatch (fun result : Output × Unit =>
    ReusableResponseDelivery.whole componentStep begin ready native code oracle caller state trace request
      (retained result.1) (input machine encode hHalt hTape result.1))

noncomputable def whole :=
  (ReusableResponseComponent.whole componentStep begin ready native code oracle caller state trace request
    P machine retained hReady hAbsorb read hRead).seq
    (delivery componentStep begin ready native code oracle caller state trace request machine retained encode hHalt hTape)
    (fun _ _ _ => rfl) (fun _ => 6 * cap + 8)
    (fun argument result h => by
      cases argument
      rw [ReusableResponseComponent.semantics] at h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨output, ho, rfl⟩ := h
      change (ReusableResponseDelivery.whole componentStep begin ready native code oracle caller state trace request
        (retained output) (input machine encode hHalt hTape output)).budget () ≤ _
      rw [ReusableResponseDelivery.budget]
      have hc := hCap output ho
      change 6 * (encode output).length + 8 ≤ _
      omega)

theorem budget :
    (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).budget () = P.budget () + (6 * cap + 9) := by
  change (P.budget () + 1) + (6 * cap + 8) = _
  omega

theorem semantics :
    (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).semantics () =
      (P.semantics ()).map (fun output => ((output, ()), (encode output, ()))) := by
  change ((ReusableResponseComponent.whole componentStep begin ready native code oracle caller state trace request
    P machine retained hReady hAbsorb read hRead).semantics ()).bind
    (fun result => ((ReusableResponseDelivery.whole componentStep begin ready native code oracle caller state trace request
      (retained result.1) (input machine encode hHalt hTape result.1)).semantics ()).map
      (fun packet => (result, packet))) = _
  rw [ReusableResponseComponent.semantics]
  simp only [ReusableResponseDelivery.semantics, PMF.pure_map, PMF.bind_map, Function.comp_def]
  rfl

theorem distribution :
    ((whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).costed ()).map
      (fun result => (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
        encode hHalt hTape cap hCap).exit () result.1) =
      (P.semantics ()).map (fun output => ReusableResponseSource.Control.source (retained output)
        (NativeCallback.resumed caller state trace request (encode output))) := by
  let W := whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
    encode hHalt hTape cap hCap
  have h := congrArg (fun distribution => distribution.map (W.exit ())) (W.correct ())
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  have he (output : Output) : W.exit () ((output, ()), (encode output, ())) =
      .source (retained output) (NativeCallback.resumed caller state trace request (encode output)) := rfl
  have hm := congrArg (fun f => (P.semantics ()).map f) (funext he)
  simpa only [W, PMF.map_comp, Function.comp_def] using h.trans hm

theorem law (horizon : Nat) (hBudget : P.budget () + (6 * cap + 9) ≤ horizon) :
    TimedExecution.eval (ReusableResponseSource.step componentStep begin ready native code oracle) horizon
      (.processing caller state trace request (P.entry ())) =
      ((whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
        encode hHalt hTape cap hCap).costed ()).bind
        (fun result => TimedExecution.eval (ReusableResponseSource.step componentStep begin ready native code oracle) (horizon - result.2)
          (.source (retained result.1.1.1) (NativeCallback.resumed caller state trace request result.1.2.1))) := by
  exact (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
    encode hHalt hTape cap hCap).law () horizon (by rw [budget]; exact hBudget)

end CryptoOracle.Interactive.ReusableResponseInvocation
