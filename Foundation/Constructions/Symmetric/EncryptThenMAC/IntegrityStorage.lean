import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityMachine
import Foundation.Crypto.Semantics.Oracle.ControllerExtent
import Foundation.Crypto.Semantics.ResourceEnvelope

/-! Count all retained tapes, temporary bit lists, private Boolean fields,
source transcript and actual signing transcript in the integrity controller.
Copies stored in different fields are counted separately. Finite code,
integer addresses and host allocation overhead are separate resources. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityStorage
open Machine Foundation.Probability
open CryptoOracle.Interactive
universe u

/-- One stored ciphertext bit followed by the stored tag. -/
def signingTrace (trace : List (Bool × List Bool)) : List (List Bool × List Bool) :=
  trace.map (fun entry => ([entry.1], entry.2))

def preparationCells : IntegrityPreparation.Control → Nat
  | .preparing _ tape => tape.cells
  | .encrypting machine => machine.tapeCells

def preparationExtent : IntegrityPreparation.Control → Nat
  | .preparing _ tape => tape.cells
  | .encrypting machine => Machine.ControllerExtent.machine machine

def controlCells : IntegrityMachine.Control → Nat
  | .initializing source generator => SourceStorage.controlCells source + generator.tapeCells
  | .source _ _ source => 2 + SourceStorage.controlCells source
  | .encrypting _ _ machine request preparation =>
      2 + machine.tapeCells + request.length + preparationCells preparation
  | .failure _ machine request => 1 + machine.tapeCells + request.length
  | .header _ machine request _ tag _ tape => 2 + machine.tapeCells + request.length + tag.length + tape.cells
  | .copying _ machine request remaining tape | .advancing _ machine request remaining tape =>
      1 + machine.tapeCells + request.length + remaining.length + tape.cells
  | .rewinding _ machine request tape => 1 + machine.tapeCells + request.length + tape.cells
  | .collecting _ machine request tape reversed =>
      1 + machine.tapeCells + request.length + tape.cells + reversed.length
  | .reversing _ machine request remaining response =>
      1 + machine.tapeCells + request.length + remaining.length + response.length

def controlExtent : IntegrityMachine.Control → Nat
  | .initializing source generator =>
      max 1 (max (ControllerExtent.controlExtent source) (Machine.ControllerExtent.machine generator))
  | .source _ _ source => max 1 (ControllerExtent.controlExtent source)
  | .encrypting _ _ machine request preparation =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (preparationExtent preparation)))
  | .failure _ machine request => max 1 (max (Machine.ControllerExtent.machine machine) request.length)
  | .header _ machine request _ tag _ tape =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (max tag.length tape.cells)))
  | .copying _ machine request remaining tape | .advancing _ machine request remaining tape =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (max remaining.length tape.cells)))
  | .rewinding _ machine request tape =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length tape.cells))
  | .collecting _ machine request tape reversed =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (max tape.cells reversed.length)))
  | .reversing _ machine request remaining response =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (max remaining.length response.length)))

def cells {State : Type u} (stateSize : State → Nat) (frame : IntegrityMachine.Frame State) : Nat :=
  stateSize frame.state + controlCells frame.control + SourceStorage.traceCells frame.sourceTrace +
    SourceStorage.traceCells (signingTrace frame.signingTrace)

def extent {State : Type u} (stateSize : State → Nat) (frame : IntegrityMachine.Frame State) : Nat :=
  max (stateSize frame.state) (max (controlExtent frame.control)
    (max (ControllerExtent.traceExtent frame.sourceTrace)
      (ControllerExtent.traceExtent (signingTrace frame.signingTrace))))

def bound (extent : Nat) : Nat := 4 * extent ^ 2 + 7 * extent + 2

theorem bound_monotone : Monotone bound := by
  intro a b h
  have hp := Nat.pow_le_pow_left h 2
  unfold bound
  omega

theorem preparation_cells (control : IntegrityPreparation.Control) :
    preparationCells control ≤ 2 * preparationExtent control := by
  cases control with
  | preparing phase tape => simp only [preparationCells, preparationExtent]; omega
  | encrypting machine => exact Machine.ControllerExtent.machine_cells machine

theorem control_cells (control : IntegrityMachine.Control) :
    controlCells control ≤ 6 * controlExtent control + 2 := by
  cases control with
  | initializing source generator =>
      have hs := ControllerExtent.control_cells source
      have hm := Machine.ControllerExtent.machine_cells generator
      simp only [controlCells, controlExtent]
      omega
  | source key used source =>
      have hs := ControllerExtent.control_cells source
      simp only [controlCells, controlExtent]
      omega
  | encrypting key used machine request preparation =>
      have hm := Machine.ControllerExtent.machine_cells machine
      have hp := preparation_cells preparation
      simp only [controlCells, controlExtent]
      omega
  | failure key machine request =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | header key machine request ciphertext tag phase tape =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | copying key machine request remaining tape =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | advancing key machine request remaining tape =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | rewinding key machine request tape =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | collecting key machine request tape reversed =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega
  | reversing key machine request remaining response =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [controlCells, controlExtent]
      omega

/-- Structural coverage counts both transcripts and every simultaneously
retained copy, without any reachability or well-formedness assumption. -/
theorem cells_bound {State : Type u} (stateSize : State → Nat) (frame : IntegrityMachine.Frame State) :
    cells stateSize frame ≤ bound (extent stateSize frame) := by
  have hc := control_cells frame.control
  have hs := ControllerExtent.trace_cells frame.sourceTrace
  have ht := ControllerExtent.trace_cells (signingTrace frame.signingTrace)
  have hsE : ControllerExtent.traceExtent frame.sourceTrace ≤ extent stateSize frame := by
    simp only [extent]; omega
  have htE : ControllerExtent.traceExtent (signingTrace frame.signingTrace) ≤ extent stateSize frame := by
    simp only [extent]; omega
  have hcE : controlExtent frame.control ≤ extent stateSize frame := by simp only [extent]; omega
  have hfE : stateSize frame.state ≤ extent stateSize frame := by simp only [extent]; omega
  have hsp := Nat.pow_le_pow_left hsE 2
  have htp := Nat.pow_le_pow_left htE 2
  unfold cells bound
  omega

end Foundation.Symmetric.EncryptThenMAC.IntegrityStorage
