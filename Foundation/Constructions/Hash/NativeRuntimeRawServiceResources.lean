import Foundation.Constructions.Hash.NativeRuntimeRawService
import Foundation.Constructions.Hash.NativeRuntimeRawResources
import Foundation.Crypto.Semantics.Oracle.PacketResponseResources

/-! Physical caller, raw hash launch and response loading share one storage
bound. Fixed hash code and prior history remain counted in every phase.
This bounds prefixes without assuming syntax validity or termination. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n κ : Nat}

def runtimeRawSavedSize (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) : Nat :=
  max (ControllerExtent.traceExtent prior)
    (NativePacketComponent.Resources.frameSize (tableSize n κ) saved)

def runtimeRawComponentBound (s : Nat) : Nat := 1024 * s ^ 2 + 2048 * s + 1024

def runtimeRawSavedBound (s : Nat) : Nat := 144 * s ^ 2 + 372 * s + 172

theorem runtimeRawComponentBound_mono : Monotone runtimeRawComponentBound := by
  intro a b h
  have hq := Nat.pow_le_pow_left h 2
  dsimp [runtimeRawComponentBound]
  omega

theorem runtimeRawSavedBound_mono : Monotone runtimeRawSavedBound := by
  intro a b h
  have hq := Nat.pow_le_pow_left h 2
  dsimp [runtimeRawSavedBound]
  omega

theorem runtimeRawSaved_encoding (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) :
    ((ConfigurationEncoding.frame (tableEncoding n κ)).encode saved).length ≤
      runtimeRawSavedBound (runtimeRawSavedSize prior saved) := by
  have h := NativePacketComponent.Resources.frame_encoding_length (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le) saved
  have hs : NativePacketComponent.Resources.frameSize (tableSize n κ) saved ≤
      runtimeRawSavedSize prior saved := Nat.le_max_right _ _
  have hq := Nat.pow_le_pow_left hs 2
  dsimp [runtimeRawSavedBound]
  omega

theorem runtimeRawBegin_size (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) (request : List Bool) :
    NativePacketLaunch.Resources.size (tableSize n κ) prior (runtimeRawBegin saved request) ≤
      max (runtimeRawSavedSize prior saved) request.length + 0 := by
  simp only [runtimeRawBegin, NativePacketLaunch.Resources.size, runtimeRawSavedSize,
    NativePacketComponent.Resources.frameSize, NativePacketService.Resources.size,
    NativePacketService.Resources.pc, NativePacketService.Resources.extent, Tape.cells,
    List.length_nil, ControllerExtent.frameExtent]
  omega

theorem runtimeRawReady_size (prior : List (List Bool × List Bool))
    (component : NativePacketLaunch.Control (IdealTable n κ))
    (saved : Configuration (IdealTable n κ)) (packet : List Bool)
    (ready : runtimeRawReady component = some (saved, packet)) :
    runtimeRawSavedSize prior saved ≤ NativePacketLaunch.Resources.size (tableSize n κ) prior component + 0 ∧
      packet.length ≤ NativePacketLaunch.Resources.size (tableSize n κ) prior component + 0 := by
  cases component with
  | preparing state loader => simp [runtimeRawReady] at ready
  | running component =>
      cases component with
      | computing frame => simp [runtimeRawReady, NativePacketComponent.ready] at ready
      | exporting frame exporter =>
          cases exporter <;> simp only [runtimeRawReady, NativePacketComponent.ready] at ready
          all_goals try contradiction
          case returned bits =>
            cases ready
            simp only [runtimeRawSavedSize, NativePacketLaunch.Resources.size,
              NativePacketComponent.Resources.size, NativePacketComponent.Resources.exportSize,
              ControllerEncoding.exportPc, Machine.ControllerExtent.exportExtent]
            omega

/-- Include the fixed native hash environment even while the caller alone
runs, or the response loader holds the saved native frame. -/
def runtimeRawCallerEncoding {State : Type*} (ES : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (Machine.ConfigurationEncoding.bit.prod
    (ConfigurationEncoding.trace.prod
      (PacketResponseEncoding.completeEncoding
        (NativePacketLaunch.Resources.encoding (tableEncoding n κ)) ES
        (ConfigurationEncoding.frame (tableEncoding n κ)))))

/-- All supported intermediate states of the actual caller controller.
The component lookup/draw is atomic in time; its full table is stored. -/
theorem runtimeRawCaller_encoded_peak {State : Type*} (ES : FiniteBitEncoding State)
    (stateSize : State → Nat) (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (callerCode : Code) (callerOracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (callerOracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start target : PacketResponseSource.Control (NativePacketLaunch.Control (IdealTable n κ)) State
      (Configuration (IdealTable n κ)))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon)
    (support : target ∈ (TimedExecution.eval
      (PacketResponseSource.step
        (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList)
          (idealCompression n κ) false prior)
        runtimeRawBegin runtimeRawReady callerCode callerOracle) elapsed start).support) :
    ((runtimeRawCallerEncoding (n := n) (κ := κ) ES).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, false, prior, callerCode, [], target)).length ≤
    2 * (EncodedStorage.codeEncoding.encode (runtimeLinkedHashCode initial.toList terminal.toList)).length +
      2 * (ConfigurationEncoding.trace.encode prior).length + 5 +
      PacketResponseEncoding.bitBoundWith callerCode [] runtimeRawComponentBound runtimeRawSavedBound
        (PacketResponseGrowth.size (NativePacketLaunch.Resources.size (tableSize n κ) prior)
          stateSize (runtimeRawSavedSize prior) start) horizon
        (PacketResponseGrowth.increment callerCode
          (NativePacketComponent.Resources.increment (runtimeLinkedHashCode initial.toList terminal.toList)
            (entryIncrement n κ) n) 0 0 stateIncrement responseCap) := by
  have he := PacketResponseResources.peak_with_bounds
    (NativePacketLaunch.Resources.encoding (tableEncoding n κ)) ES
    (ConfigurationEncoding.frame (tableEncoding n κ))
    (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
    runtimeRawBegin runtimeRawReady callerCode callerOracle []
    (NativePacketLaunch.Resources.size (tableSize n κ) prior) stateSize (runtimeRawSavedSize prior)
    runtimeRawComponentBound runtimeRawSavedBound runtimeRawComponentBound_mono runtimeRawSavedBound_mono
    (NativePacketComponent.Resources.increment (runtimeLinkedHashCode initial.toList terminal.toList)
      (entryIncrement n κ) n) 0 0 stateIncrement responseCap
    (NativePacketLaunch.Resources.encoding_length (tableEncoding n κ) (tableSize n κ)
      (fun state => (tableEncoding_length _ _ state).le) prior)
    hState (runtimeRawSaved_encoding prior)
    (NativePacketLaunch.Resources.step_size (tableSize n κ)
      (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior
      (entryIncrement n κ) n (fun state request answer ha => by
        have h := idealCompression_growth n κ state request answer ha
        exact ⟨h.1, h.2.le⟩))
    (runtimeRawBegin_size prior) (runtimeRawReady_size prior) hOracle
    start target horizon elapsed within support
  simp only [runtimeRawCallerEncoding, FiniteBitEncoding.prod_encode_length,
    Machine.ConfigurationEncoding.bit, List.length_singleton]
  omega

end Foundation.Hash.Native
