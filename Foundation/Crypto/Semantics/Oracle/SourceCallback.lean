import Foundation.Crypto.Semantics.Oracle.SourceEntry

/-! Contracts for the actual outer source controller. Native/export work
stops at its first returned packet, then the response loader and the final
ownership transfer execute. Post-return source time is never frozen. -/
namespace CryptoOracle.Interactive.SourceEntry
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

def embedLoader (key second : Machine.Tape) (frame : Configuration State) : Control State :=
  .handling saved state trace request (.calling key second (.source frame))

theorem writing_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (remaining before : List Bool) :
    TimedExecution.eval (step native code oracle) (2 * remaining.length + 1)
      (embedLoader saved state trace request key second ⟨state, .loading saved remaining
        { left := before.reverse.map some }, published⟩) =
      PMF.pure (embedLoader saved state trace request key second
        ⟨state, .rewinding saved { left := (before ++ remaining).reverse.map some }, published⟩) := by
  induction remaining generalizing before with
  | nil =>
      simp [TimedExecution.eval, step, embedLoader, PreparedCallback.step, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega,
        TimedExecution.eval]
      simp only [step, embedLoader, PreparedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      rw [TimedExecution.eval]
      simp only [step, PreparedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [embedLoader, Machine.Tape.write, Machine.Tape.moveRight, List.reverse_append,
        List.map_append, List.append_assoc] using ih (before ++ [bit])

theorem rewind_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (left.length + 1)
      (embedLoader saved state trace request key second
        ⟨state, .rewinding saved ⟨left.map some, current, right⟩, published⟩) =
      PMF.pure (embedLoader saved state trace request key second
        ⟨state, .running { saved with outputTape := ResponseLoading.fromCells (left.reverse.map some ++ current :: right) }, published⟩) := by
  induction left generalizing current right with
  | nil =>
      simp [TimedExecution.eval, step, embedLoader, PreparedCallback.step, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
        transition, ResponseLoading.fromCells, PMF.pure_map]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, embedLoader, PreparedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, List.map_cons, Machine.Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
      simp only [embedLoader] at ih
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- The actual response loader reaches the outer controller's first resume
point. Its transcript is a runtime value, not rebuilt by a proof reader. -/
theorem loading_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (packet : List Bool) :
    TimedExecution.eval (step native code oracle) (3 * packet.length + 2)
      (embedLoader saved state trace request key second ⟨state, .loading saved packet {}, published⟩) =
      PMF.pure (embedLoader saved state trace request key second
        ⟨state, .running { saved with outputTape := ResponseLoading.loaded packet }, published⟩) := by
  rw [show 3 * packet.length + 2 = (2 * packet.length + 1) + (packet.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add]
  have h := writing_run native code oracle saved state trace request published key second packet []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at h
  rw [h, PMF.pure_bind, rewind_run]
  simp [embedLoader, ResponseLoading.loaded]

theorem packet_return (key second : Machine.Tape) (packet : List Bool) :
    TimedExecution.eval (step native code oracle) (3 * packet.length + 4)
      (.handling saved state trace request (.calling key second (.responding (.returned packet)))) =
      PMF.pure (.source key (NativeCallback.resumed saved state trace request packet)) := by
  rw [show 3 * packet.length + 4 = ((3 * packet.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [step, PreparedCallback.step, NativeCallback.step, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (step native code oracle) (3 * packet.length + 2) 1]
  have h := loading_run native code oracle saved state trace request ((request, packet) :: trace) key second packet
  change (TimedExecution.eval (step native code oracle) (3 * packet.length + 2)
    (embedLoader saved state trace request key second
      ⟨state, .loading saved packet {}, (request, packet) :: trace⟩)).bind
    (TimedExecution.eval (step native code oracle) 1) = _
  rw [h, PMF.pure_bind]
  simpa only [embedLoader, NativeCallback.resumed] using resume_transfer native code oracle key second saved
    { saved with outputTape := ResponseLoading.loaded packet } state state trace ((request, packet) :: trace) request

def embedExport (frame : Machine.ResponseExport.Control × (Machine.Tape × Machine.Tape)) : Control State :=
  .handling saved state trace request (.calling frame.2.1 frame.2.2 (.responding frame.1))

def exportedBoundary : Control State → Bool
  | .handling _ _ _ _ (.calling _ _ (.responding component)) => NativeCallback.exportBoundary component
  | _ => true

variable {Input : Type v} {Output : Type w}

noncomputable def exportBody (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input) :=
  ((NativeCallback.exported P encode hHalt hTape read hRead cap hCap).frame
    (Machine.Tape × Machine.Tape)).liftBoundary (fun frame => NativeCallback.exportBoundary frame.1)
    (fun _ _ _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, framedStep, Machine.ResponseExport.step, PMF.pure_map])
    (fun _ frame => NativeCallback.packetRead frame.1) (fun _ _ => rfl)
    (step P.code code oracle) exportedBoundary (embedExport saved state trace request)
    (fun _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, step, embedExport,
        PreparedCallback.step, NativeCallback.step, framedStep, PMF.map_comp, Function.comp_def])

def preparationBoundary : Control State → Bool
  | .handling _ _ _ _ (.preparing preparation) => PreparedCallback.boundary preparation
  | _ => true

noncomputable def preparationBody :=
  Machine.PairPreparation.procedure.liftBoundary PreparedCallback.boundary (fun _ _ _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [PreparedCallback.boundary, Machine.PairPreparation.step])
    (fun _ _ => ()) (fun _ _ => rfl) (step native code oracle) preparationBoundary
    (fun preparation => Control.handling saved state trace request (.preparing preparation)) (fun _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [PreparedCallback.boundary, step,
      PreparedCallback.step, PMF.map_comp, Function.comp_def])

noncomputable def preparationHandoff : Procedure (step native code oracle) (Machine.PairPreparation.Input × Unit) Unit :=
  Procedure.ofFixed (step native code oracle)
    (fun input => .handling saved state trace request (.preparing (Machine.PairPreparation.procedure.exit input.1 input.2)))
    (fun input _ => .handling saved state trace request (.calling
      (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (Machine.PairPreparation.operand [] input.1.second input.1.secondTail)
      (.responding (.running { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.1.first input.1.second).map some ++ [none]) }))))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by simp [TimedExecution.eval, step, PreparedCallback.step,
      Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map])

noncomputable def preparationPrefix :=
  (preparationBody native code oracle saved state trace request).remember.seq
    (preparationHandoff native code oracle saved state trace request)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem preparation_semantics (input : Machine.PairPreparation.Input) :
    (preparationPrefix native code oracle saved state trace request).semantics input = PMF.pure ((input, ()), ()) := by
  simp [preparationPrefix, preparationBody, preparationHandoff, Procedure.seq, Procedure.remember,
    Procedure.liftBoundary, Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map]

noncomputable def reply : Procedure (step native code oracle) (Machine.PairPreparation.Input × List Bool) Unit :=
  Procedure.ofFixed (step native code oracle)
    (fun input => .handling saved state trace request (.calling
      (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (Machine.PairPreparation.operand [] input.1.second input.1.secondTail) (.responding (.returned input.2))))
    (fun input _ => .source (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (NativeCallback.resumed saved state trace request input.2))
    (fun _ => PMF.pure ()) (fun input => 3 * input.2.length + 4)
    (fun input => by
      simpa only [PMF.pure_map] using packet_return native code oracle saved state trace request
        (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
        (Machine.PairPreparation.operand [] input.1.second input.1.secondTail) input.2)

section Composition
variable (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (view : Machine.PairPreparation.Input → Input)
    (hEntry : ∀ input, P.execution.entry (view input) =
      { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.first input.second).map some ++ [none]) })

noncomputable def body :=
  (preparationPrefix P.code code oracle saved state trace request).seq
    ((exportBody code oracle saved state trace request P encode hHalt hTape read hRead cap hCap).reindex
      (fun result => (view result.1.1, (Machine.PairPreparation.operand [] result.1.1.first result.1.1.firstTail,
        Machine.PairPreparation.operand [] result.1.1.second result.1.1.secondTail))))
    (fun input result hResult => by
      rw [preparation_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      change Control.handling _ _ _ _ (.calling _ _ (.responding (.running (P.execution.entry (view input))))) = _
      rw [hEntry]
      rfl)
    (fun input => P.execution.budget (view input) + (3 * cap (view input) + 4))
    (fun input result hResult => by
      rw [preparation_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      exact Nat.le_refl _)

theorem body_semantics (input : Machine.PairPreparation.Input) :
    (body code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry).semantics input =
      (P.execution.semantics (view input)).map (fun output => (((input, ()), ()), encode output)) := by
  simp only [body, Procedure.seq]
  rw [preparation_semantics, PMF.pure_bind]
  simp only [exportBody, Procedure.reindex, Procedure.liftBoundary, Procedure.frame, NativeCallback.exported,
    Procedure.ofFixed, PMF.map_comp, Function.comp_def]

noncomputable def handler :=
  (body code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry).seq
    ((reply P.code code oracle saved state trace request).reindex (fun result => (result.1.1.1, result.2)))
    (fun _ _ _ => rfl) (fun input => 3 * cap (view input) + 4)
    (fun input result hResult => by
      rw [body_semantics, PMF.mem_support_map_iff] at hResult
      obtain ⟨output, hOutput, he⟩ := hResult
      subst result
      have h := hCap (view input) output hOutput
      change 3 * (encode output).length + 4 ≤ 3 * cap (view input) + 4
      omega)

theorem handler_budget (input : Machine.PairPreparation.Input) :
    (handler code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry).budget input =
      12 * input.first.length + P.execution.budget (view input) + 6 * cap (view input) + 12 := by
  change (12 * input.first.length + 3 + 1) + (P.execution.budget (view input) + (3 * cap (view input) + 4)) +
    (3 * cap (view input) + 4) = _
  omega

theorem handler_distribution (input : Machine.PairPreparation.Input) :
    ((handler code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry).costed input).map
      (fun result => (handler code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry).exit input result.1) =
      (P.execution.semantics (view input)).map (fun output => Control.source
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (NativeCallback.resumed saved state trace request (encode output))) := by
  let H := handler code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry
  change (H.costed input).map (H.exit input ∘ Prod.fst) = _
  rw [← PMF.map_comp, H.correct]
  simp only [H, handler, Procedure.seq]
  rw [body_semantics]
  simp only [reply, Procedure.reindex, Procedure.ofFixed, PMF.map_bind,
    PMF.pure_map, Function.comp_def, PMF.bind_map]
  simp only [PMF.map, Function.comp_def]

/-- A complete single source call, for arbitrary source code and saved PC.
The source tape supplies the request and the existing private tape supplies
the first operand. The residual law continues the outer source controller. -/
noncomputable def invoke (machine : Machine.Configuration) (key : Machine.Tape)
    (input : Machine.PairPreparation.Input)
    (hSaved : saved = machine.advance) (hRequest : request = input.second)
    (hStore : key = Machine.PairPreparation.operand [] input.first input.firstTail)
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hSourceTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second) := by
  let H := handler code oracle saved state trace request P encode hHalt hTape read hRead cap hCap view hEntry
  let I : Procedure (step P.code code oracle) Unit Unit := Procedure.ofFixed (step P.code code oracle)
    (fun _ => .source key ⟨state, .running machine, trace⟩)
    (fun _ _ => H.entry input) (fun _ => PMF.pure ()) (fun _ => 2 * input.second.length + 4)
    (fun _ => by
      have h := call_entry P.code code oracle key machine state trace input.second [] input.secondTail hActive hCall hSourceTape
      rw [← hSaved, hStore, hSourceTape] at h
      simp only [PMF.pure_map]
      change TimedExecution.eval (step P.code code oracle) (2 * input.second.length + 4)
        (.source key ⟨state, .running machine, trace⟩) = PMF.pure (.handling saved state trace request
          (.preparing (Machine.PairPreparation.procedure.entry input)))
      simpa only [hStore, hRequest, Machine.PairPreparation.procedure, Procedure.ofFixed,
        Machine.PairPreparation.operand, Machine.PairPreparation.fromCells, RequestExport.packetTape,
        List.reverse_nil, List.map_nil, PMF.pure_map] using h)
  exact I.seq (H.reindex (fun _ => input)) (fun _ _ _ => rfl)
    (fun _ => H.budget input) (fun _ _ _ => Nat.le_refl _)

end Composition
end CryptoOracle.Interactive.SourceEntry
