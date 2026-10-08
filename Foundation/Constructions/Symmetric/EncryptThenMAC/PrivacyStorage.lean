import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyMachine
import Foundation.Crypto.Semantics.Oracle.ControllerExtent
import Foundation.Crypto.Semantics.ResourceEnvelope

/-! Retained data in the entire native privacy controller. The generated
key store, signer's private input, saved caller, temporary response and both
histories are counted separately whenever simultaneously present. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyStorage
open Machine Foundation.Probability CryptoOracle.Interactive
universe u

def generatorCells : PrivateKeyGeneration.Control → Nat
  | .generating machine => machine.tapeCells
  | .rewinding tape | .ready tape => tape.cells

def generatorExtent : PrivateKeyGeneration.Control → Nat
  | .generating machine => Machine.ControllerExtent.machine machine
  | .rewinding tape | .ready tape => tape.cells

def responderCells : ResponseHandoff.Control → Nat
  | .headerWriting key remaining buffer | .headerAdvancing key remaining buffer =>
      key.cells + remaining.length + buffer.cells
  | .copying machine => machine.tapeCells
  | .rewinding key buffer => key.cells + buffer.cells
  | .authenticating key machine => key.cells + machine.tapeCells

def responderExtent : ResponseHandoff.Control → Nat
  | .headerWriting key remaining buffer | .headerAdvancing key remaining buffer =>
      max key.cells (max remaining.length buffer.cells)
  | .copying machine => Machine.ControllerExtent.machine machine
  | .rewinding key buffer => max key.cells buffer.cells
  | .authenticating key machine => max key.cells (Machine.ControllerExtent.machine machine)

def controlCells : PrivacyMachine.Control → Nat
  | .initializing source generator => SourceStorage.controlCells source + generatorCells generator
  | .source key source => key.cells + SourceStorage.controlCells source
  | .responding machine request responder => machine.tapeCells + request.length + responderCells responder
  | .rewinding key machine request tape => key.cells + machine.tapeCells + request.length + tape.cells
  | .collecting key machine request tape reversed =>
      key.cells + machine.tapeCells + request.length + tape.cells + reversed.length
  | .reversing key machine request remaining response =>
      key.cells + machine.tapeCells + request.length + remaining.length + response.length

def controlExtent : PrivacyMachine.Control → Nat
  | .initializing source generator => max 1 (max (ControllerExtent.controlExtent source) (generatorExtent generator))
  | .source key source => max 1 (max key.cells (ControllerExtent.controlExtent source))
  | .responding machine request responder =>
      max 1 (max (Machine.ControllerExtent.machine machine) (max request.length (responderExtent responder)))
  | .rewinding key machine request tape =>
      max 1 (max key.cells (max (Machine.ControllerExtent.machine machine) (max request.length tape.cells)))
  | .collecting key machine request tape reversed =>
      max 1 (max key.cells (max (Machine.ControllerExtent.machine machine)
        (max request.length (max tape.cells reversed.length))))
  | .reversing key machine request remaining response =>
      max 1 (max key.cells (max (Machine.ControllerExtent.machine machine)
        (max request.length (max remaining.length response.length))))

def cells {State : Type u} (stateSize : State → Nat) (frame : PrivacyMachine.Frame State) : Nat :=
  stateSize frame.state + controlCells frame.control + SourceStorage.traceCells frame.sourceTrace +
    SourceStorage.traceCells frame.externalTrace

def extent {State : Type u} (stateSize : State → Nat) (frame : PrivacyMachine.Frame State) : Nat :=
  max (stateSize frame.state) (max (controlExtent frame.control)
    (max (ControllerExtent.traceExtent frame.sourceTrace) (ControllerExtent.traceExtent frame.externalTrace)))

def bound (extent : Nat) : Nat := 4 * extent ^ 2 + 7 * extent + 2

theorem bound_monotone : Monotone bound := by
  intro a b h
  have hp := Nat.pow_le_pow_left h 2
  unfold bound
  omega

theorem generator_cells (generator : PrivateKeyGeneration.Control) :
    generatorCells generator ≤ 2 * generatorExtent generator := by
  cases generator with
  | generating machine => exact Machine.ControllerExtent.machine_cells machine
  | rewinding tape => simp only [generatorCells, generatorExtent]; omega
  | ready tape => simp only [generatorCells, generatorExtent]; omega

theorem responder_cells (responder : ResponseHandoff.Control) :
    responderCells responder ≤ 3 * responderExtent responder := by
  cases responder with
  | headerWriting key remaining buffer => simp only [responderCells, responderExtent]; omega
  | headerAdvancing key remaining buffer => simp only [responderCells, responderExtent]; omega
  | copying machine =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [responderCells, responderExtent]
      omega
  | rewinding key buffer => simp only [responderCells, responderExtent]; omega
  | authenticating key machine =>
      have hm := Machine.ControllerExtent.machine_cells machine
      simp only [responderCells, responderExtent]
      omega

theorem control_cells (control : PrivacyMachine.Control) :
    controlCells control ≤ 6 * controlExtent control + 1 := by
  cases control with
  | initializing source generator =>
      have hs := ControllerExtent.control_cells source
      have hg := generator_cells generator
      simp only [controlCells, controlExtent]
      omega
  | source key source =>
      have hs := ControllerExtent.control_cells source
      simp only [controlCells, controlExtent]
      omega
  | responding machine request responder =>
      have hm := Machine.ControllerExtent.machine_cells machine
      have hr := responder_cells responder
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

/-- Both histories and all simultaneous copies are covered in every state,
including malformed states; no hidden reachability premise is used. -/
theorem cells_bound {State : Type u} (stateSize : State → Nat) (frame : PrivacyMachine.Frame State) :
    cells stateSize frame ≤ bound (extent stateSize frame) := by
  have hc := control_cells frame.control
  have hs := ControllerExtent.trace_cells frame.sourceTrace
  have ht := ControllerExtent.trace_cells frame.externalTrace
  have hsE : ControllerExtent.traceExtent frame.sourceTrace ≤ extent stateSize frame := by
    simp only [extent]; omega
  have htE : ControllerExtent.traceExtent frame.externalTrace ≤ extent stateSize frame := by
    simp only [extent]; omega
  have hcE : controlExtent frame.control ≤ extent stateSize frame := by simp only [extent]; omega
  have hfE : stateSize frame.state ≤ extent stateSize frame := by simp only [extent]; omega
  have hsp := Nat.pow_le_pow_left hsE 2
  have htp := Nat.pow_le_pow_left htE 2
  unfold cells bound
  omega

end Foundation.Symmetric.EncryptThenMAC.PrivacyStorage
