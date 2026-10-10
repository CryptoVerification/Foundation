import Foundation.Crypto.Semantics.Oracle.PacketResponseTerminal
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Charge an actual caller halt after a packet service. The private retained
frame is kept; a component's halt is never treated as caller termination. -/
namespace CryptoOracle.Interactive.PacketResponseHalt
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

variable {State : Type*}

def Ready (code : Code) (frame : Configuration State) : Prop :=
  ∃ machine, frame.control = .running machine ∧ machine.halted = false ∧ code[machine.pc]? = some (.native .halt)

def halted (frame : Configuration State) : Configuration State :=
  match frame.control with
  | .running machine => { frame with control := .running { machine with halted := true } }
  | _ => frame

theorem halted_terminal (code : Code) (frame : Configuration State) (h : Ready code frame) :
    Reification.terminal (halted frame).control = true := by
  rcases frame with ⟨state, control, trace⟩
  obtain ⟨machine, he, _, _⟩ := h
  dsimp only at he
  subst control
  rfl

variable {Component Saved : Type*} (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component) (ready : Component → Option (Saved × List Bool))
    (code : Code) (oracle : BitOracle State)

theorem halt_step (saved : Saved) (frame : Configuration State) (h : Ready code frame) :
    PacketResponseSource.step componentStep begin ready code oracle (.source saved frame) =
      PMF.pure (.source saved (halted frame)) := by
  rcases frame with ⟨state, control, trace⟩
  obtain ⟨machine, he, active, lookup⟩ := h
  dsimp only at he
  subst control
  simp [PacketResponseSource.step, Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, active, lookup, Machine.Instruction.next, halted, PMF.pure_map]

noncomputable def procedure :=
  Procedure.ofFixed (PacketResponseSource.step componentStep begin ready code oracle)
    (fun source : {source : Saved × Configuration State // Ready code source.2} => .source source.val.1 source.val.2)
    (fun _ (output : Saved × Configuration State) => .source output.1 output.2)
    (fun source => PMF.pure (source.val.1, halted source.val.2)) (fun _ => 1)
    (fun source => by simp only [TimedExecution.eval, halt_step componentStep begin ready code oracle _ _ source.property,
      PMF.pure_bind, PMF.pure_map])

theorem procedure_operational : Procedure.Operational (procedure componentStep begin ready code oracle) := by
  apply Procedure.operational_ofFixed
end CryptoOracle.Interactive.PacketResponseHalt
