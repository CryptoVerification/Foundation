import Foundation.Crypto.Semantics.Oracle.OneUseSourceInterval
import Foundation.Crypto.Semantics.Oracle.OneUseSourceHalt

/-! A finite caller samples its actual request bit before invoking the common
arbitrary-width handler. Both the random source instruction and physical
request processing are charged. The private key need not have length one. -/
namespace Foundation.OneUseRandomRequestExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def code : Code := [.native (.randomBit .output), .call, .native .halt]

def initialMachine (input : List Bool) : Machine.Configuration :=
  { inputTape := Machine.Tape.ofBits input, outputTape := RequestExport.packetTape [] [] [false] }

def atCall (input : List Bool) (bit : Bool) : Machine.Configuration :=
  { initialMachine input with pc := 1, outputTape := RequestExport.packetTape [] [] [bit] }

def frame (input : List Bool) (state : State) (trace : List (List Bool × List Bool)) (bit : Bool) :
    Configuration State := ⟨state, .running (atCall input bit), trace⟩

variable (oracle : BitOracle State) (spent : Bool) (key : List Bool)
    (keyTail : List (Option Bool)) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool))

noncomputable def sourceInterval :=
  (OneUseSourceInterval.interval Machine.OneTimePad.Prepared.listProcedure.code code oracle spent
    (Machine.PairPreparation.operand [] key keyTail) 1).reindex
      (fun _ : Unit => ⟨state, .running (initialMachine input), trace⟩)

theorem source_distribution :
    (sourceInterval oracle spent key keyTail input state trace).semantics () =
      sampleBit.map (frame input state trace) := by
  simp only [sourceInterval, Procedure.reindex, OneUseSourceInterval.interval, Procedure.interval]
  simp [runToBoundary, OneUseSourceInterval.boundary, initialMachine, code,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, Machine.Instruction.next, Machine.Configuration.updateTape,
    Machine.Configuration.advance, RequestExport.packetTape, Machine.Tape.write,
    PMF.pure_map, PMF.map_bind]
  rw [PMF.map]
  congr 1
  funext bit
  cases bit <;> simp [frame, atCall, initialMachine, RequestExport.packetTape]

/-- Recovering the entire frame from the sampled bit is proved only on the
supported exits. No tape or private state is erased by this observation. -/
noncomputable def sample :=
  (sourceInterval oracle spent key keyTail input state trace).observe
    (fun frame => match frame.control with
      | .running machine => machine.outputTape.current.getD false
      | _ => false)
    (fun _ bit => OneUseSourceInterval.embed spent (Machine.PairPreparation.operand [] key keyTail)
      (frame input state trace bit))
    (by
      intro _ output hOutput
      rw [source_distribution, PMF.mem_support_map_iff] at hOutput
      obtain ⟨bit, _, he⟩ := hOutput
      subst output
      cases bit <;> rfl)

theorem sample_semantics :
    (sample oracle spent key keyTail input state trace).semantics () = sampleBit := by
  change ((sourceInterval oracle spent key keyTail input state trace).semantics ()).map _ = _
  rw [source_distribution, PMF.map_comp]
  have he : (fun output : Configuration State => match output.control with
      | .running machine => machine.outputTape.current.getD false
      | _ => false) ∘ frame input state trace = id := by
    funext bit
    cases bit <;> rfl
  rw [he, PMF.map_id]

noncomputable def handler (bit : Bool) :=
  OneUseXorRequest.invocation code oracle (atCall input bit) state trace key [bit] keyTail []
    (by rfl) (by rfl) (by rfl) spent

noncomputable def experiment :=
  (sample oracle spent key keyTail input state trace).seq
    (Procedure.dispatch (handler oracle spent key keyTail input state trace))
    (fun _ bit _ => by
      simp only [Procedure.dispatch, handler]
      rw [OneUseXorRequest.entry]
      rfl)
    (fun _ => 33 * (key.length + 1) + 33)
    (fun _ bit _ => by
      simp only [Procedure.dispatch, handler]
      rw [OneUseXorRequest.invocation_budget]
      exact OneUseXorRequest.budget_le key [bit] spent)

theorem experiment_budget :
    (experiment oracle spent key keyTail input state trace).budget () =
      1 + (33 * (key.length + 1) + 33) := rfl

theorem experiment_semantics :
    (experiment oracle spent key keyTail input state trace).semantics () =
      sampleBit.bind (fun bit => PMF.pure
        (bit, OneUseXorRequest.result (atCall input bit) state trace key [bit] keyTail spent)) := by
  change ((sample oracle spent key keyTail input state trace).semantics ()).bind _ = _
  rw [sample_semantics]
  congr 1
  funext bit
  simp only [Procedure.dispatch, handler, OneUseXorRequest.semantics, PMF.pure_map]

def returnedMachine (bit : Bool) : Machine.Configuration :=
  { (atCall input bit).advance with outputTape := ResponseLoading.loaded (OneUseXorRequest.reply spent key [bit]) }

noncomputable def finish (bit : Bool) :=
  OneUseSourceHalt.halt Machine.OneTimePad.Prepared.listProcedure.code code oracle
    (OneUseXorRequest.used spent key [bit]) (Machine.PairPreparation.operand [] key keyTail)
    (returnedMachine spent key input bit) state (([bit], OneUseXorRequest.reply spent key [bit]) :: trace)
    (by rfl) (by rfl)

theorem experiment_exit (bit : Bool) (output : OneUseSource.Control State) :
    (experiment oracle spent key keyTail input state trace).exit () (bit, output) = output := by
  change (handler oracle spent key keyTail input state trace bit).exit () output = output
  unfold handler
  cases spent <;> simp only [OneUseXorRequest.invocation, Bool.false_eq_true, ↓reduceIte]
  · split <;> rfl
  · rfl

noncomputable def stop :=
  (Procedure.dispatch (finish oracle spent key keyTail input state trace)).reindex
    (fun result : Bool × OneUseSource.Control State => result.1)

noncomputable def complete :=
  (experiment oracle spent key keyTail input state trace).seq
    (stop oracle spent key keyTail input state trace)
    (fun _ middle hs => by
      rw [experiment_semantics, PMF.mem_support_bind_iff] at hs
      obtain ⟨bit, _, hs⟩ := hs
      rw [PMF.mem_support_pure_iff] at hs
      subst middle
      rw [experiment_exit]
      rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

def halted (bit : Bool) :=
  OneUseSourceHalt.final (OneUseXorRequest.used spent key [bit])
    (Machine.PairPreparation.operand [] key keyTail) (returnedMachine spent key input bit)
    state (([bit], OneUseXorRequest.reply spent key [bit]) :: trace)

theorem complete_budget :
    (complete oracle spent key keyTail input state trace).budget () =
      2 + (33 * (key.length + 1) + 33) := by
  change (experiment oracle spent key keyTail input state trace).budget () + 1 = _
  rw [experiment_budget]
  omega

theorem complete_semantics :
    (complete oracle spent key keyTail input state trace).semantics () =
      sampleBit.map (fun bit =>
        ((bit, OneUseXorRequest.result (atCall input bit) state trace key [bit] keyTail spent),
          halted spent key keyTail input state trace bit)) := by
  change ((experiment oracle spent key keyTail input state trace).semantics ()).bind _ = _
  rw [experiment_semantics, PMF.bind_bind]
  simp only [PMF.pure_bind, stop, Procedure.reindex, Procedure.dispatch, finish,
    OneUseSourceHalt.halt, Procedure.ofFixed, Function.comp_def, PMF.pure_map]
  rw [PMF.map]
  rfl

/-- Entire execution, including the random native instruction, real query
validation/delivery, and real caller halt. Key width and initial use status
are unrestricted. No fuel-exhausted state is identified with a final state. -/
theorem run (horizon : Nat) (hBudget : 2 + (33 * (key.length + 1) + 33) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (.source spent (Machine.PairPreparation.operand [] key keyTail)
        ⟨state, .running (initialMachine input), trace⟩) =
      sampleBit.map (halted spent key keyTail input state trace) := by
  have h := (complete oracle spent key keyTail input state trace).final_run ()
    (fun output hs => by
      rw [complete_semantics, PMF.mem_support_map_iff] at hs
      obtain ⟨bit, _, he⟩ := hs
      subst output
      exact OneUseSourceHalt.absorbing Machine.OneTimePad.Prepared.listProcedure.code code oracle
        (OneUseXorRequest.used spent key [bit]) (Machine.PairPreparation.operand [] key keyTail)
        (returnedMachine spent key input bit) state (([bit], OneUseXorRequest.reply spent key [bit]) :: trace))
    horizon (by rw [complete_budget]; exact hBudget)
  rw [complete_semantics, PMF.map_comp] at h
  exact h

/-- Bound every actual intermediate state of the full finite caller, not
only the query handler or the halted output. Existing tapes and key suffixes
are counted through the whole-controller initial extent. -/
theorem memory_peak (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ 2 + (33 * (key.length + 1) + 33))
    (target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) elapsed
      (.source spent (Machine.PairPreparation.operand [] key keyTail)
        ⟨state, .running (initialMachine input), trace⟩)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      4 * (ControllerExtent.sourceExtent stateSize
        (.source spent (Machine.PairPreparation.operand [] key keyTail)
          ⟨state, .running (initialMachine input), trace⟩) +
        (2 + (33 * (key.length + 1) + 33)) * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.sourceExtent stateSize
        (.source spent (Machine.PairPreparation.operand [] key keyTail)
          ⟨state, .running (initialMachine input), trace⟩) +
        (2 + (33 * (key.length + 1) + 33)) * (stateIncrement + responseCap + 2)) + 2 :=
by
  have hExtent := ResourceGrowth.prefix_bound
    (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
    (ControllerExtent.sourceExtent stateSize) (stateIncrement + responseCap + 2)
    (ControllerExtent.source_step stateSize Machine.OneTimePad.Prepared.listProcedure.code code oracle
      stateIncrement responseCap hOracle) (2 + (33 * (key.length + 1) + 33)) elapsed hElapsed
    (.source spent (Machine.PairPreparation.operand [] key keyTail)
      ⟨state, .running (initialMachine input), trace⟩) target h
  have hCells := ControllerExtent.source_cells stateSize target
  have hPow := Nat.pow_le_pow_left hExtent 2
  omega

end Foundation.OneUseRandomRequestExamples
