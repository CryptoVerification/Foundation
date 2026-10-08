import Foundation.Crypto.Semantics.Machine.ControllerExtent
import Foundation.Crypto.Semantics.Oracle.ControllerStorage

/-! Largest retained data object and transcript length in private controllers.
All copies are measured in storage, while copying does not enlarge extent.
A bound on extent gives a polynomial bound on the complete retained data. -/
namespace CryptoOracle.Interactive.ControllerExtent
open Foundation.Probability
universe u
variable {State : Type u}

def traceExtent : List (List Bool × List Bool) → Nat
  | [] => 0
  | (request, response) :: rest =>
      max (rest.length + 1) (max request.length (max response.length (traceExtent rest)))

def controlExtent : Control → Nat
  | .running c => Machine.ControllerExtent.machine c
  | .sending c tape reversed => max (Machine.ControllerExtent.machine c) (max tape.cells reversed.length)
  | .reversing c remaining request => max (Machine.ControllerExtent.machine c) (max remaining.length request.length)
  | .awaiting c request => max (Machine.ControllerExtent.machine c) request.length
  | .loading c remaining tape | .advancing c remaining tape =>
      max (Machine.ControllerExtent.machine c) (max remaining.length tape.cells)
  | .rewinding c tape => max (Machine.ControllerExtent.machine c) tape.cells
  | .finished _ => 1

def frameExtent (stateSize : State → Nat) (frame : Configuration State) : Nat :=
  max (stateSize frame.state) (max (controlExtent frame.control) (traceExtent frame.reverseTrace))

def callbackExtent (stateSize : State → Nat) : NativeCallback.Control State → Nat
  | .responding component => Machine.ControllerExtent.exportExtent component
  | .source frame => frameExtent stateSize frame

def checkedExtent (stateSize : State → Nat) : CheckedCallback.Control State → Nat
  | .preparing preparation => Machine.ControllerExtent.check preparation
  | .computing first second component =>
      max first.cells (max second.cells (Machine.ControllerExtent.exportExtent component))
  | .tagging first second packet => max first.cells (max second.cells (Machine.ControllerExtent.packet packet))
  | .calling first second callback => max first.cells (max second.cells (callbackExtent stateSize callback))

def sourceExtent (stateSize : State → Nat) : OneUseSource.Control State → Nat
  | .source _ key frame => max key.cells (frameExtent stateSize frame)
  | .handling _ saved state trace request handler =>
      max (Machine.ControllerExtent.machine saved) (max (stateSize state)
        (max (traceExtent trace) (max request.length (checkedExtent stateSize handler))))

def initializationExtent (stateSize : State → Nat) (caller : Configuration State) :
    OneUseInitialization.Control State → Nat
  | .initializing component => max (frameExtent stateSize caller) (Machine.ControllerExtent.initialization component)
  | .active source => sourceExtent stateSize source

theorem trace_length (trace : List (List Bool × List Bool)) : trace.length ≤ traceExtent trace := by
  cases trace <;> simp only [traceExtent, List.length_nil, List.length_cons] <;> omega

theorem trace_cells_cap (trace : List (List Bool × List Bool)) (cap : Nat) (h : traceExtent trace ≤ cap) :
    SourceStorage.traceCells trace ≤ 2 * cap * trace.length := by
  induction trace with
  | nil => simp [SourceStorage.traceCells]
  | cons entry rest ih =>
      rcases entry with ⟨request, response⟩
      simp only [traceExtent] at h
      have ht := ih (by omega)
      simp only [SourceStorage.traceCells, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem trace_cells (trace : List (List Bool × List Bool)) :
    SourceStorage.traceCells trace ≤ 2 * (traceExtent trace) ^ 2 := by
  have hb := trace_cells_cap trace (traceExtent trace) (Nat.le_refl _)
  have hl := trace_length trace
  nlinarith

theorem control_cells (control : Control) : SourceStorage.controlCells control ≤ 4 * controlExtent control + 1 := by
  cases control <;> simp only [SourceStorage.controlCells, controlExtent,
    Machine.ControllerExtent.machine, Machine.Configuration.tapeCells] <;> omega

theorem frame_cells (stateSize : State → Nat) (frame : Configuration State) :
    SourceStorage.cells stateSize frame ≤ 2 * (frameExtent stateSize frame) ^ 2 + 5 * frameExtent stateSize frame + 1 := by
  have hc := control_cells frame.control
  have ht := trace_cells frame.reverseTrace
  have hm : traceExtent frame.reverseTrace ≤ frameExtent stateSize frame := by
    simp only [frameExtent]; omega
  have hq : (traceExtent frame.reverseTrace) ^ 2 ≤ (frameExtent stateSize frame) ^ 2 := Nat.pow_le_pow_left hm 2
  have hs : stateSize frame.state ≤ frameExtent stateSize frame := by simp only [frameExtent]; omega
  have hd : controlExtent frame.control ≤ frameExtent stateSize frame := by simp only [frameExtent]; omega
  simp only [SourceStorage.cells, frameExtent] at *
  nlinarith

theorem callback_cells (stateSize : State → Nat) (control : NativeCallback.Control State) :
    ControllerStorage.callbackCells stateSize control ≤
      2 * (callbackExtent stateSize control) ^ 2 + 5 * callbackExtent stateSize control + 1 := by
  cases control with
  | responding component =>
      have hb := Machine.ControllerExtent.export_cells component
      simp only [ControllerStorage.callbackCells, callbackExtent]
      nlinarith
  | source frame => exact frame_cells stateSize frame

theorem checked_cells (stateSize : State → Nat) (control : CheckedCallback.Control State) :
    ControllerStorage.checkedCells stateSize control ≤
      2 * (checkedExtent stateSize control) ^ 2 + 7 * checkedExtent stateSize control + 2 := by
  cases control with
  | preparing preparation =>
      have hb := Machine.ControllerExtent.check_cells preparation
      simp only [ControllerStorage.checkedCells, checkedExtent]
      nlinarith
  | computing first second component =>
      have hb := Machine.ControllerExtent.export_cells component
      simp only [ControllerStorage.checkedCells, checkedExtent]
      omega
  | tagging first second packet =>
      have hb := Machine.ControllerExtent.packet_cells packet
      simp only [ControllerStorage.checkedCells, checkedExtent]
      omega
  | calling first second callback =>
      have hb := callback_cells stateSize callback
      have hm : callbackExtent stateSize callback ≤ checkedExtent stateSize (.calling first second callback) := by
        simp only [checkedExtent]; omega
      have hq := Nat.pow_le_pow_left hm 2
      have ha : first.cells ≤ checkedExtent stateSize (.calling first second callback) := by simp only [checkedExtent]; omega
      have hb' : second.cells ≤ checkedExtent stateSize (.calling first second callback) := by simp only [checkedExtent]; omega
      simp only [ControllerStorage.checkedCells, checkedExtent] at *
      nlinarith

theorem source_cells (stateSize : State → Nat) (control : OneUseSource.Control State) :
    ControllerStorage.sourceCells stateSize control ≤
      4 * (sourceExtent stateSize control) ^ 2 + 11 * sourceExtent stateSize control + 2 := by
  cases control with
  | source used key frame =>
      have hb := frame_cells stateSize frame
      have hm : frameExtent stateSize frame ≤ sourceExtent stateSize (.source used key frame) := by
        simp only [sourceExtent]; omega
      have hq := Nat.pow_le_pow_left hm 2
      have hk : key.cells ≤ sourceExtent stateSize (.source used key frame) := by simp only [sourceExtent]; omega
      simp only [ControllerStorage.sourceCells, sourceExtent] at *
      nlinarith
  | handling used saved state trace request handler =>
      have hs := Machine.ControllerExtent.machine_cells saved
      have ht := trace_cells trace
      have hh := checked_cells stateSize handler
      have hm : checkedExtent stateSize handler ≤ sourceExtent stateSize (.handling used saved state trace request handler) := by
        simp only [sourceExtent]; omega
      have hn : traceExtent trace ≤ sourceExtent stateSize (.handling used saved state trace request handler) := by
        simp only [sourceExtent]; omega
      have hq := Nat.pow_le_pow_left hm 2
      have hr := Nat.pow_le_pow_left hn 2
      have hm' : Machine.ControllerExtent.machine saved ≤ sourceExtent stateSize (.handling used saved state trace request handler) := by simp only [sourceExtent]; omega
      have hs' : stateSize state ≤ sourceExtent stateSize (.handling used saved state trace request handler) := by simp only [sourceExtent]; omega
      have hreq : request.length ≤ sourceExtent stateSize (.handling used saved state trace request handler) := by simp only [sourceExtent]; omega
      simp only [ControllerStorage.sourceCells, sourceExtent] at *
      nlinarith

theorem initialization_cells (stateSize : State → Nat) (caller : Configuration State)
    (control : OneUseInitialization.Control State) :
    ControllerStorage.initializationCells stateSize caller control ≤
      4 * (initializationExtent stateSize caller control) ^ 2 + 11 * initializationExtent stateSize caller control + 2 := by
  cases control with
  | initializing component =>
      have hf := frame_cells stateSize caller
      have hc := Machine.ControllerExtent.initialization_cells component
      have hm : frameExtent stateSize caller ≤ initializationExtent stateSize caller (.initializing component) := by
        simp only [initializationExtent]; omega
      have hq := Nat.pow_le_pow_left hm 2
      have hc' : Machine.ControllerExtent.initialization component ≤ initializationExtent stateSize caller (.initializing component) := by simp only [initializationExtent]; omega
      simp only [ControllerStorage.initializationCells, initializationExtent] at *
      nlinarith
  | active source => exact source_cells stateSize source

end CryptoOracle.Interactive.ControllerExtent
