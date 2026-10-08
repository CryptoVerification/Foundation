import Foundation.Crypto.Semantics.Oracle.RetainedResponseDelivery
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! A charged boundary between an arbitrary certified component and physical
response delivery. The readiness view exposes an existing native machine and
retained frame. Its concrete instantiation must not compute a fresh packet. -/
namespace CryptoOracle.Interactive.ComponentResponseCallback
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false

inductive Control (Component : Type u) (State : Type v) (Saved : Type w) where
  | processing (component : Component)
  | delivering (frame : NativeCallback.Control State × Saved)

variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def step : Control Component State Saved → PMF (Control Component State Saved)
  | .processing component =>
      match ready component with
      | some frame => PMF.pure (.delivering (.responding (.running frame.1), frame.2))
      | none => (componentStep component).map .processing
  | .delivering frame =>
      (framedStep (NativeCallback.step native code oracle caller state trace request) frame).map .delivering

def componentBoundary (component : Component) : Bool := (ready component).isSome

def boundary : Control Component State Saved → Bool
  | .processing component => componentBoundary ready component
  | .delivering _ => true

variable {Output : Type x} (P : Procedure componentStep Unit Output)
    (machine : Output → Machine.Configuration) (retained : Output → Saved)
    (hReady : ∀ output, ready (P.exit () output) = some (machine output, retained output))
    (hAbsorb : ∀ component, componentBoundary ready component = true → componentStep component = PMF.pure component)
    (read : Component → Output) (hRead : ∀ output, read (P.exit () output) = output)

noncomputable def body :=
  P.liftBoundary (componentBoundary ready)
    (fun _ output _ => by cases ‹Unit›; simp [componentBoundary, hReady]) hAbsorb
    (fun _ => read) (fun _ output => by cases ‹Unit›; exact hRead output)
    (step componentStep ready native code oracle caller state trace request)
    (boundary ready) Control.processing (fun _ => rfl)
    (by
      intro component h
      cases hr : ready component with
      | none => simp [step, hr]
      | some frame => simp [componentBoundary, hr] at h)

/-- This ownership transfer consumes one transition and preserves the
entire native machine and retained frame supplied at the physical exit. -/
noncomputable def transfer :
    Procedure (step componentStep ready native code oracle caller state trace request) Output Unit :=
  Procedure.ofFixed _
    (fun output => .processing (P.exit () output))
    (fun output _ => .delivering (.responding (.running (machine output)), retained output))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun output => by simp [TimedExecution.eval, step, hReady, PMF.pure_map])

variable (encode : Output → List Bool)
    (hHalt : ∀ output, (machine output).halted = true)
    (hTape : ∀ output, (machine output).outputTape = Machine.ResponseExport.endTape (encode output))

def deliveryInput (output : Output) : RetainedResponseDelivery.Input :=
  ⟨machine output, encode output, hHalt output, hTape output⟩

noncomputable def delivery :=
  Procedure.dispatch (fun output : Output =>
    (((RetainedResponseDelivery.framed native code oracle caller state trace request
      (deliveryInput machine encode hHalt hTape output) Saved).reindex
      (fun _ : Unit => ((), retained output))).transport
      (step componentStep ready native code oracle caller state trace request)
      Control.delivering (fun _ => rfl)))

theorem delivery_budget (output : Output) :
    (delivery componentStep ready native code oracle caller state trace request machine retained encode hHalt hTape).budget output =
      6 * (encode output).length + 7 :=
  RetainedResponseDelivery.framed_budget native code oracle caller state trace request
    (deliveryInput machine encode hHalt hTape output) (retained output)

theorem delivery_semantics (output : Output) :
    (delivery componentStep ready native code oracle caller state trace request machine retained encode hHalt hTape).semantics output =
      PMF.pure (encode output, ()) :=
  RetainedResponseDelivery.framed_semantics native code oracle caller state trace request
    (deliveryInput machine encode hHalt hTape output) (retained output)

noncomputable def after :=
  (transfer componentStep ready native code oracle caller state trace request P machine retained hReady).remember.seq
    ((delivery componentStep ready native code oracle caller state trace request machine retained encode hHalt hTape).reindex
      (fun result : Output × Unit => result.1))
    (fun _ _ _ => rfl) (fun output => 6 * (encode output).length + 7)
    (fun output result h => by
      change result ∈ ((PMF.pure ()).map (fun result => (output, result))).support at h
      simp only [PMF.pure_map, PMF.mem_support_pure_iff] at h
      subst result
      change (delivery componentStep ready native code oracle caller state trace request machine retained encode hHalt hTape).budget output ≤ _
      rw [delivery_budget])

theorem after_budget (output : Output) :
    (after componentStep ready native code oracle caller state trace request P machine retained hReady encode hHalt hTape).budget output =
      6 * (encode output).length + 8 := by
  change 1 + (6 * (encode output).length + 7) = _
  omega

theorem after_semantics (output : Output) :
    (after componentStep ready native code oracle caller state trace request P machine retained hReady encode hHalt hTape).semantics output =
      PMF.pure ((output, ()), (encode output, ())) := by
  change ((PMF.pure ()).map (fun result => (output, result))).bind
    (fun result => ((delivery componentStep ready native code oracle caller state trace request machine retained encode hHalt hTape).semantics result.1).map
      (fun packet => (result, packet))) = _
  simp only [PMF.pure_map, PMF.pure_bind, delivery_semantics]

variable (cap : Nat) (hCap : ∀ output ∈ (P.semantics ()).support, (encode output).length ≤ cap)

noncomputable def whole :=
  (body componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).seq
    (after componentStep ready native code oracle caller state trace request P machine retained hReady encode hHalt hTape)
    (fun _ _ _ => rfl) (fun _ => 6 * cap + 8)
    (fun input output h => by
      cases input
      rw [after_budget]
      have hc := hCap output h
      omega)

theorem whole_budget :
    (whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).budget () = P.budget () + (6 * cap + 8) := rfl

theorem whole_semantics :
    (whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).semantics () =
      (P.semantics ()).map (fun output => (output, ((output, ()), (encode output, ())))) := by
  change (P.semantics ()).bind (fun output =>
    ((after componentStep ready native code oracle caller state trace request P machine retained hReady encode hHalt hTape).semantics output).map
      (fun packet => (output, packet))) = _
  simp only [after_semantics, PMF.pure_map]
  rfl

/-- The endpoint law retains the actual cost distribution separately. -/
theorem whole_distribution :
    ((whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
      encode hHalt hTape cap hCap).costed ()).map
      (fun result => (whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
        encode hHalt hTape cap hCap).exit () result.1) =
      (P.semantics ()).map (fun output => Control.delivering
        (.source (NativeCallback.resumed caller state trace request (encode output)), retained output)) := by
  let W := whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
    encode hHalt hTape cap hCap
  have h := congrArg (fun distribution => distribution.map (W.exit ())) (W.correct ())
  rw [whole_semantics, PMF.map_comp] at h
  have he (output : Output) : W.exit () (output, ((output, ()), (encode output, ()))) =
      Control.delivering (.source (NativeCallback.resumed caller state trace request (encode output)), retained output) := rfl
  simp only [PMF.map_comp, Function.comp_def] at h
  have hm := congrArg (fun f => (P.semantics ()).map f) (funext he)
  simpa only [W, PMF.map_comp, Function.comp_def] using h.trans hm

/-- After the actual component duration and delivery duration, remaining
steps execute the caller with its loaded response and extended transcript. -/
theorem whole_law (horizon : Nat) (hBudget : P.budget () + (6 * cap + 8) ≤ horizon) :
    TimedExecution.eval (step componentStep ready native code oracle caller state trace request) horizon
      (.processing (P.entry ())) =
      ((whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
        encode hHalt hTape cap hCap).costed ()).bind
        (fun result => TimedExecution.eval (step componentStep ready native code oracle caller state trace request)
          (horizon - result.2)
          (.delivering (.source (NativeCallback.resumed caller state trace request result.1.2.2.1),
            retained result.1.2.1.1))) := by
  exact (whole componentStep ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead
    encode hHalt hTape cap hCap).law () horizon hBudget

end CryptoOracle.Interactive.ComponentResponseCallback
