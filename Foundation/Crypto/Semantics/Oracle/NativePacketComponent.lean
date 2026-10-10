import Foundation.Crypto.Semantics.Oracle.ReificationExecution
import Foundation.Crypto.Semantics.Oracle.ResponseLoading
import Foundation.Crypto.Semantics.Machine.CellResponseExport

/-! Continue a native interactive component with the existing physical packet
exporter. The entire completed native frame remains retained while its output
tape is scanned. Readiness exposes the packet created by that scan, never an
unexecuted semantic encoder. -/
namespace CryptoOracle.Interactive.NativePacketComponent
open Foundation.Probability TimedExecution Machine
universe u
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | computing (frame : Configuration State)
  | exporting (frame : Configuration State) (exporter : Machine.ResponseExport.Control)

variable {State : Type u}

noncomputable def step (code : Code) (oracle : BitOracle State) : Control State → PMF (Control State)
  | .computing frame =>
      if Reification.terminal frame.control then
        match frame.control with
        | .running machine => PMF.pure (.exporting frame (.running machine))
        | _ => PMF.pure (.exporting frame (.returned []))
      else (Reification.timedStep code oracle frame).map .computing
  | .exporting frame exporter =>
      (Machine.CellResponseExport.step [] exporter).map (.exporting frame)

def ready : Control State → Option (Configuration State × List Bool)
  | .exporting frame (.returned packet) => some (frame, packet)
  | _ => none

def read : Control State → Configuration State × List Bool
  | .computing frame => (frame, [])
  | .exporting frame (.returned packet) => (frame, packet)
  | .exporting frame _ => (frame, [])

def boundary : Control State → Bool
  | .computing frame => Reification.terminal frame.control
  | .exporting _ _ => true

theorem ready_absorbing (code : Code) (oracle : BitOracle State) (control : Control State)
    (h : (ready control).isSome = true) : step code oracle control = PMF.pure control := by
  cases control with
  | computing => simp [ready] at h
  | exporting frame exporter =>
      cases exporter <;> simp_all [ready, step, Machine.CellResponseExport.step, PMF.pure_map]

/-- Exact transported exporter transitions, including every scan and reversal. -/
theorem exporting_run (code : Code) (oracle : BitOracle State)
    (frame : Configuration State) (exporter : Machine.ResponseExport.Control) (fuel : Nat) :
    TimedExecution.eval (step code oracle) fuel (.exporting frame exporter) =
      (TimedExecution.eval (Machine.CellResponseExport.step []) fuel exporter).map (.exporting frame) := by
  induction fuel generalizing exporter with
  | zero => simp [TimedExecution.eval, PMF.pure_map]
  | succ fuel ih =>
      simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]

/-- One ownership transfer followed by physical export from the head. The
retained native frame, including private table and trace, is unchanged. -/
theorem export_cells_run (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (packet : List Bool)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseLoading.loaded packet)) :
    TimedExecution.eval (step code oracle) (2 * packet.length + 5)
      (.computing ⟨state, .running machine, trace⟩) =
    PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.returned packet)) := by
  rw [show 2 * packet.length + 5 = 1 + (2 * packet.length + 4) by omega, eval_add]
  have first : TimedExecution.eval (step code oracle) 1 (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.running machine)) := by
    simp [TimedExecution.eval, step, Reification.terminal, halted]
  rw [first, PMF.pure_bind, exporting_run]
  have exported := Machine.CellResponseExport.run_fromHead [] machine packet halted layout
  rw [exported, PMF.pure_map]

/-- Preserve the exact-layout interface as a specialization of the
cell-aware exporter. Existing valid-layout budgets remain unchanged. -/
theorem export_run (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (packet : List Bool)
    (halted : machine.halted = true)
    (layout : machine.outputTape = ResponseLoading.loaded packet) :
    TimedExecution.eval (step code oracle) (2 * packet.length + 5)
      (.computing ⟨state, .running machine, trace⟩) =
    PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.returned packet)) := by
  apply export_cells_run code oracle state machine trace packet halted
  rw [layout]
  exact Machine.Tape.Equivalent.refl _

end CryptoOracle.Interactive.NativePacketComponent
