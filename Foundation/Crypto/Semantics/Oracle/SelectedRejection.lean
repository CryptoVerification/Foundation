import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedurePublicComposition
import Foundation.Crypto.Semantics.Oracle.RejectionTiming
import Foundation.Crypto.Semantics.KeyedIteration

/-! Arbitrary proved request-selection programs compose with actual rejection.
The descriptor is public and contains the physical call preconditions.
No particular source code, random instruction, key distribution, or one-bit
request is built into this interface. -/
namespace CryptoOracle.Interactive.SelectedRejection
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} {code : Code}

structure Call (State : Type u) (code : Code) (width : Nat) where
  machine : Machine.Configuration
  state : State
  trace : List (List Bool × List Bool)
  request : List Bool
  tail : List (Option Bool)
  active : machine.halted = false
  instruction : code[machine.pc]? = some .call
  tape : machine.outputTape = RequestExport.packetTape [] tail request
  mismatch : width ≠ request.length

abbrev Output := Unit × ((Unit × Unit) × (List Bool × Unit))

def input (key : List Bool) (keyTail : List (Option Bool)) (hKey : key.length = width)
    (call : Call State code width) : Machine.PreparationCheck.FailureInput :=
  ⟨key, call.request, keyTail, call.tail, by simpa only [hKey] using call.mismatch⟩

variable (native : Machine.Program) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool)) (hKey : key.length = width)

noncomputable def reject (call : Call State code width) :
    Procedure (OneUseSource.step native code oracle) Unit Output :=
  OneUseSource.rejectedInvocation native code oracle call.machine call.state call.trace
    call.active call.instruction (input key keyTail hKey call) call.tape

def returned (call : Call State code width) : Configuration State :=
  NativeCallback.resumed call.machine.advance call.state call.trace call.request [false]

/-- A key-free public kernel. The all-false list is used only in the analysis
of preparation cost, and is never inserted into the executed machine. -/
noncomputable def kernel (keyTail : List (Option Bool)) (call : Call State code width) :
    PMF (Option (Configuration State) × Nat) :=
  let reference := input (List.replicate width false) keyTail (List.length_replicate ..) call
  (RejectionTiming.costs (12 * Machine.PreparationCheck.consumed reference + 10)
    (RejectionTiming.initial reference)).map fun result =>
      (some (returned call), 2 * call.request.length + result.2 + 19)

theorem reject_public_cost (call : Call State code width) :
    ((reject native oracle key keyTail hKey call).costed ()).map
      (fun result => (RejectionTiming.publicExit
        ((reject native oracle key keyTail hKey call).exit () result.1), result.2)) =
      kernel keyTail call := by
  unfold reject kernel
  rw [RejectionTiming.rejected_invocation_costs]
  have hp := RejectionTiming.preparation_cost_independence native native code code oracle oracle
    call.machine.advance call.machine.advance call.state call.state call.trace call.trace
    call.request call.request (input key keyTail hKey call)
    (input (List.replicate width false) keyTail (List.length_replicate ..) call)
    (by simp [input, hKey]) rfl rfl rfl
  change RejectionTiming.costs
      (12 * Machine.PreparationCheck.consumed (input key keyTail hKey call) + 10)
      (RejectionTiming.initial (input key keyTail hKey call)) = _ at hp
  rw [hp]
  rfl

theorem reject_exit (call : Call State code width) (output : Output)
    (h : output ∈ ((reject native oracle key keyTail hKey call).semantics ()).support) :
    (reject native oracle key keyTail hKey call).exit () output =
      .source false (Machine.PairPreparation.operand [] key keyTail) (returned call) := by
  rw [← Procedure.correct, PMF.mem_support_map_iff] at h
  obtain ⟨result, hResult, he⟩ := h
  subst output
  exact RejectionTiming.rejected_invocation_retains_key native code oracle call.machine
    call.state call.trace call.active call.instruction (input key keyTail hKey call) call.tape result hResult

variable {Input : Type v}
    (selection : Procedure (OneUseSource.step native code oracle) Input (Call State code width))
    (handoff : ∀ start call, call ∈ (selection.semantics start).support →
      (reject native oracle key keyTail hKey call).entry () = selection.exit start call)
    (cap : Input → Nat)
    (hCap : ∀ start call, call ∈ (selection.semantics start).support →
      (reject native oracle key keyTail hKey call).budget () ≤ cap start)

/-- Selection executes the existing caller and returns its actual call
configuration. Capture, preparation, rejection, delivery and return are charged. -/
noncomputable def selected :=
  selection.seq (Procedure.dispatch (reject native oracle key keyTail hKey))
    handoff cap hCap

theorem selected_public_cost (start : Input) (publicSelection : PMF (Call State code width × Nat))
    (hSelection : selection.costed start = publicSelection) :
    ((selected native oracle key keyTail hKey selection handoff cap hCap).costed start).map
      (fun result => (RejectionTiming.publicExit
        ((selected native oracle key keyTail hKey selection handoff cap hCap).exit start result.1), result.2)) =
      CostedComposition.bind publicSelection (kernel keyTail) := by
  apply Procedure.seq_public_cost selection (Procedure.dispatch (reject native oracle key keyTail hKey))
    handoff cap hCap id
    (fun call output => RejectionTiming.publicExit ((reject native oracle key keyTail hKey call).exit () output))
    publicSelection (kernel keyTail) start
  · change (selection.costed start).map id = publicSelection
    rw [PMF.map_id]
    exact hSelection
  · intro call
    exact reject_public_cost native oracle key keyTail hKey call

theorem selected_budget (start : Input) :
    (selected native oracle key keyTail hKey selection handoff cap hCap).budget start =
      selection.budget start + cap start := rfl

theorem selected_exit (start : Input) (output : Call State code width × Output)
    (h : output ∈ ((selected native oracle key keyTail hKey selection handoff cap hCap).semantics start).support) :
    (selected native oracle key keyTail hKey selection handoff cap hCap).exit start output =
      .source false (Machine.PairPreparation.operand [] key keyTail) (returned output.1) := by
  change output ∈ ((selection.semantics start).bind (fun call =>
    ((reject native oracle key keyTail hKey call).semantics ()).map (fun result => (call, result)))).support at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨call, _, hOutput⟩ := h
  rw [PMF.mem_support_map_iff] at hOutput
  obtain ⟨result, hResult, he⟩ := hOutput
  subst output
  exact reject_exit native oracle key keyTail hKey call result hResult

section Adaptive
variable (frame : Input → Configuration State) (next : Call State code width → Input)
    (hNext : ∀ call, frame (next call) = returned call)
    (hEntry : ∀ start, selection.entry start =
      .source false (Machine.PairPreparation.operand [] key keyTail) (frame start))

/-- Return a public logical state that recovers the exact physical exit.
This makes the real selection/rejection contract composable with its next
round; no machine reset, copy, or response is inserted for free. -/
noncomputable def round :=
  (selected native oracle key keyTail hKey selection handoff cap hCap).observe
    (fun result => next result.1)
    (fun _ result => .source false (Machine.PairPreparation.operand [] key keyTail) (frame result))
    (fun start result h => by
      rw [hNext]
      exact (selected_exit native oracle key keyTail hKey selection handoff cap hCap start result h).symm)

include hEntry in
theorem round_return (start output : Input) :
    (round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).exit start output =
      (round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).entry output :=
  (hEntry output).symm

noncomputable def roundKernel (publicSelection : Input → PMF (Call State code width × Nat)) :
    Input → PMF (Input × Nat) :=
  fun start => CostedComposition.bind (publicSelection start) (fun call =>
    (kernel keyTail call).map (fun result => (next call, result.2)))

theorem round_public_cost (publicSelection : Input → PMF (Call State code width × Nat))
    (hSelection : ∀ start, selection.costed start = publicSelection start) (start : Input) :
    (round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).costed start =
      roundKernel keyTail next publicSelection start := by
  have hSecond : ∀ call, ((reject native oracle key keyTail hKey call).costed ()).map
      (fun result => (next call, result.2)) =
      (kernel keyTail call).map (fun result => (next call, result.2)) := by
    intro call
    have h := congrArg (fun distribution => distribution.map (fun result => (next call, result.2)))
      (reject_public_cost native oracle key keyTail hKey call)
    simpa only [PMF.map_comp, Function.comp_def] using h
  simp only [round, Procedure.observe, selected, Procedure.seq, Procedure.dispatch,
    roundKernel, CostedComposition.bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [← hSelection start]
  congr 1
  funext chosen
  have h := congrArg (fun distribution => distribution.map
    (fun result => (result.1, chosen.2 + result.2))) (hSecond chosen.1)
  simpa only [PMF.map_comp, Function.comp_def] using h

include hEntry in
/-- A whole adaptive sequence of malformed requests, including the real
selection, rejection, restoration and response costs in every round. -/
theorem iterateUntil_public_cost (publicSelection : Input → PMF (Call State code width × Nat))
    (hSelection : ∀ start, selection.costed start = publicSelection start)
    (bound : Nat) (hBound : ∀ start, selection.budget start + cap start ≤ bound)
    (stop : Input → Bool) (rounds : Nat) (start : Input) :
    (((round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).iterateUntil
      stop bound hBound
      (fun initial result _ => round_return native oracle key keyTail hKey selection handoff cap hCap
        frame next hNext hEntry initial result) rounds).costed start) =
      CostedIteration.eval (CostedIteration.guarded (roundKernel keyTail next publicSelection) stop) rounds start := by
  have h := Procedure.iterateUntil_public_cost
    (round native oracle key keyTail hKey selection handoff cap hCap frame next hNext)
    bound hBound
    (fun initial result _ => round_return native oracle key keyTail hKey selection handoff cap hCap
      frame next hNext hEntry initial result)
    stop stop (roundKernel keyTail next publicSelection) id (fun _ => rfl)
    (fun initial => by
      change ((round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).costed initial).map id = _
      rw [PMF.map_id]
      exact round_public_cost native oracle key keyTail hKey selection handoff cap hCap frame next hNext
        publicSelection hSelection initial) rounds start
  change (((round native oracle key keyTail hKey selection handoff cap hCap frame next hNext).iterateUntil
    stop bound hBound _ rounds).costed start).map id = _ at h
  simpa only [PMF.map_id, id_eq] using h
end Adaptive

end CryptoOracle.Interactive.SelectedRejection
