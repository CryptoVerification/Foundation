import Foundation.Constructions.Hash.NativeRuntimeProcedure
import Foundation.Crypto.Semantics.Oracle.NativePacketComponent
import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Continue the common native hash with a real output scan and reversal.
The whole completed hash frame is retained. Proof-side readers describe this
execution; the returned packet is built by the exporter controller itself. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Proof-side view of the existing native machine, without runtime work. -/
def runtimeExportMachine {State : Type*} (frame : Configuration State) : Machine.Configuration :=
  match frame.control with
  | .running machine => machine
  | _ => {}

def runtimeExportPacket {State : Type*} (frame : Configuration State) : List Bool :=
  (runtimeExportMachine frame).outputBits

def RuntimeExportable {State : Type*} (n : Nat) (frame : Configuration State) : Prop :=
  frame.control = .running (runtimeExportMachine frame) ∧
  (runtimeExportMachine frame).halted = true ∧
  (runtimeExportMachine frame).outputTape = ResponseLoading.loaded (runtimeExportPacket frame) ∧
  (runtimeExportPacket frame).length = n

theorem typedHashFinish_exportable {n κ : Nat} (pc : Nat) (input : Tape)
    (out : Outcome (CompressionInput (Bits κ) (Bits n)) (Bits n) (Bits n)
      (CompressionTable (Bits κ) (Bits n))) :
    RuntimeExportable n (typedHashFinish pc input out) := by
  simp [RuntimeExportable, runtimeExportMachine, runtimeExportPacket, typedHashFinish,
    Machine.Configuration.outputBits, loaded_bits]

theorem runtimeExportable_support {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) (frame : Configuration (IdealTable n κ))
    (support : frame ∈ ((runtimeStoppedProcedure initial terminal).semantics input).support) :
    RuntimeExportable n frame := by
  change frame ∈ (((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
    (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeFinalInput (input.2.map Bits.toList)))).support at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, _, rfl⟩ := support
  exact typedHashFinish_exportable _ _ out

noncomputable def runtimeExportCertified {n κ : Nat} (initial : Bits n) (terminal : Bits κ) :=
  (runtimeStoppedProcedure initial terminal).certify (RuntimeExportable n)
    (runtimeExportable_support initial terminal)

/-- Totalization only supplies proof data; the exporter never calls this reader. -/
private noncomputable def runtimeExportRead {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) (frame : Configuration (IdealTable n κ)) :
    {frame : Configuration (IdealTable n κ) // RuntimeExportable n frame} := by
  classical
  exact if h : RuntimeExportable n frame then ⟨frame, h⟩ else
    ((runtimeExportCertified initial terminal).semantics input).support_nonempty.choose

private theorem runtimeExportRead_exit {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) (frame : {frame : Configuration (IdealTable n κ) // RuntimeExportable n frame}) :
    runtimeExportRead initial terminal input ((runtimeExportCertified initial terminal).exit input frame) = frame := by
  classical
  apply Subtype.ext
  change (runtimeExportRead initial terminal input frame.val).val = frame.val
  simp [runtimeExportRead, frame.property]

/-- Hash execution is embedded without changing its transitions before halt. -/
noncomputable def runtimePacketBody {n κ : Nat} (initial : Bits n) (terminal : Bits κ) :=
  (runtimeExportCertified initial terminal).liftBoundary
    (fun frame => Reification.terminal frame.control)
    (fun _ frame _ => by
      change Reification.terminal frame.val.control = true
      rw [frame.property.1]
      exact frame.property.2.1)
    (fun frame halted => by simp [Reification.timedStep, halted])
    (runtimeExportRead initial terminal) (runtimeExportRead_exit initial terminal)
    (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
    NativePacketComponent.boundary NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame notHalted => by simp [NativePacketComponent.step, notHalted])

/-- Transfer the existing halted machine to the exporter. Its physical tape
is retained, then actually scanned and reversed. -/
noncomputable def runtimePacketDelivery {n κ : Nat} (initial : Bits n) (terminal : Bits κ) :
    Procedure (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      {frame : Configuration (IdealTable n κ) // RuntimeExportable n frame} Unit :=
  Procedure.ofFixed _ (fun frame => .computing frame.val)
    (fun frame _ => .exporting frame.val (.returned (runtimeExportPacket frame.val)))
    (fun _ => PMF.pure ()) (fun _ => 2 * n + 5)
    (fun frame => by
      have h := NativePacketComponent.export_run
        (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
        frame.val.state (runtimeExportMachine frame.val) frame.val.reverseTrace
        (runtimeExportPacket frame.val) frame.property.2.1 frame.property.2.2.1
      have frame_eq : (⟨frame.val.state, .running (runtimeExportMachine frame.val), frame.val.reverseTrace⟩ : Configuration (IdealTable n κ)) = frame.val := by
        exact congrArg (fun control : Interactive.Control =>
          (⟨frame.val.state, control, frame.val.reverseTrace⟩ : Configuration (IdealTable n κ))) frame.property.1.symm
      rw [frame_eq, frame.property.2.2.2] at h
      simpa only [PMF.pure_map] using h)

noncomputable def runtimePacketWhole {n κ : Nat} (initial : Bits n) (terminal : Bits κ) :=
  (runtimePacketBody initial terminal).seq (runtimePacketDelivery initial terminal)
    (fun _ _ _ => rfl) (fun _ => 2 * n + 5) (fun _ _ _ => Nat.le_refl _)

/-- Return the full physical frame and the packet produced by the exporter. -/
noncomputable def runtimePacketProcedure {n κ : Nat} (initial : Bits n) (terminal : Bits κ) :=
  (runtimePacketWhole initial terminal).observe
    (fun result => (result.1.val, runtimeExportPacket result.1.val))
    (fun _ result => .exporting result.1 (.returned result.2)) (fun _ _ _ => rfl)

theorem runtimePacketProcedure_budget {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) :
    (runtimePacketProcedure initial terminal).budget input =
      runtimeHashSteps n κ input.2.length + (2 * n + 5) := rfl

/-- Certification and physical export preserve the original joint hash
state/digest/transcript law. Export does not resample or replace its table. -/
theorem runtimePacketProcedure_semantics {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) :
    (runtimePacketProcedure initial terminal).semantics input =
      (((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
        (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeFinalInput (input.2.map Bits.toList)))).map
        (fun frame => (frame, runtimeExportPacket frame)) := by
  change (((runtimeExportCertified initial terminal).semantics input).bind
    (fun frame => (PMF.pure ()).map (fun unitArg => (frame, unitArg)))).map
    (fun result => (result.1.val, runtimeExportPacket result.1.val)) = _
  simp only [PMF.pure_map, PMF.map_bind]
  have erased := (runtimeStoppedProcedure initial terminal).certify_semantics
    (RuntimeExportable n) (runtimeExportable_support initial terminal) input
  change _ = ((runtimeStoppedProcedure initial terminal).semantics input).map
    (fun frame => (frame, runtimeExportPacket frame))
  rw [← erased, PMF.map_comp]
  rfl

/-- The packet produced by the physical exporter has the exact tag width. -/
theorem runtimePacketProcedure_response_length {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) (output : Configuration (IdealTable n κ) × List Bool)
    (support : output ∈ ((runtimePacketProcedure initial terminal).semantics input).support) :
    output.2.length = n := by
  rw [runtimePacketProcedure_semantics, PMF.mem_support_map_iff] at support
  obtain ⟨frame, hFrame, rfl⟩ := support
  rw [PMF.mem_support_map_iff] at hFrame
  obtain ⟨out, _, rfl⟩ := hFrame
  exact (typedHashFinish_exportable _ _ out).2.2.2

end Foundation.Hash.Native
