import Foundation.Crypto.Semantics.Oracle.PacketResponseSource
import Foundation.Crypto.Semantics.Oracle.StructuredCodeStorage
import Foundation.Crypto.Semantics.Machine.NativePacketServiceResources

/-! Local growth of all retained objects in an arbitrary packet-response
caller. Component launch and ready views have explicit size obligations.
Copying requests into the trace is counted by trace extent, not ignored. -/
namespace CryptoOracle.Interactive.PacketResponseGrowth
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {Component : Type u} {State : Type v} {Saved : Type w}

def machineSize (machine : Machine.Configuration) : Nat :=
  max 1 (max machine.pc (Machine.ControllerExtent.machine machine))

def frameSize (stateSize : State → Nat) (frame : Configuration State) : Nat :=
  max 1 (max (ConfigurationEncoding.pc frame.control) (ControllerExtent.frameExtent stateSize frame))

def size (componentSize : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat) :
    PacketResponseSource.Control Component State Saved → Nat
  | .source retained frame => max (savedSize retained) (frameSize stateSize frame)
  | .processing caller state trace request component =>
      max (machineSize caller) (max (stateSize state) (max (ControllerExtent.traceExtent trace)
        (max request.length (componentSize component))))
  | .returning retained caller state trace loader =>
      max (savedSize retained) (max (machineSize caller) (max (stateSize state)
        (max (ControllerExtent.traceExtent trace) (NativePacketService.Resources.size loader))))

variable (componentStep : Component → PMF Component) (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool)) (code : Code) (oracle : BitOracle State)
    (componentSize : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat)
    (componentIncrement beginIncrement readyIncrement stateIncrement responseCap : Nat)
    (hComponent : ∀ start next, next ∈ (componentStep start).support → componentSize next ≤ componentSize start + componentIncrement)
    (hBegin : ∀ retained request, componentSize (begin retained request) ≤ max (savedSize retained) request.length + beginIncrement)
    (hReady : ∀ component retained packet, ready component = some (retained, packet) →
      savedSize retained ≤ componentSize component + readyIncrement ∧ packet.length ≤ componentSize component + readyIncrement)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

def increment : Nat := EncodedStorage.addressCap code + componentIncrement + beginIncrement + readyIncrement + stateIncrement + responseCap + 3

include hComponent hBegin hReady hOracle in
theorem step_bound (start next : PacketResponseSource.Control Component State Saved)
    (h : next ∈ (PacketResponseSource.step componentStep begin ready code oracle start).support) :
    size componentSize stateSize savedSize next ≤ size componentSize stateSize savedSize start +
      increment code componentIncrement beginIncrement readyIncrement stateIncrement responseCap := by
  cases start with
  | source retained frame =>
      cases hc : frame.control with
      | awaiting caller request =>
          simp only [PacketResponseSource.step, hc, PMF.mem_support_pure_iff] at h
          subst next
          have hb := hBegin retained request
          simp only [size, frameSize, machineSize, ControllerExtent.frameExtent, hc,
            ControllerExtent.controlExtent, ConfigurationEncoding.pc, increment]
          omega
      | _ =>
          simp only [PacketResponseSource.step, hc, PMF.mem_support_map_iff] at h
          obtain ⟨after, ha, rfl⟩ := h
          have hp := EncodedStorage.pc_step code oracle frame after ha
          have he := ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle frame after ha
          simp only [size, frameSize, increment]
          omega
  | processing caller state trace request component =>
      cases hr : ready component with
      | none =>
          simp only [PacketResponseSource.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨after, ha, rfl⟩ := h
          have hb := hComponent component after ha
          simp only [size, increment]
          omega
      | some output =>
          rcases output with ⟨retained, packet⟩
          simp only [PacketResponseSource.step, hr, PMF.mem_support_pure_iff] at h
          subst next
          obtain ⟨hs, hp⟩ := hReady component retained packet hr
          have ht := ControllerExtent.trace_length trace
          simp only [size, increment, ControllerExtent.traceExtent, List.length_cons,
            NativePacketService.Resources.size, NativePacketService.Resources.pc,
            NativePacketService.Resources.extent, Tape.cells, List.length_nil]
          omega
  | returning retained caller state trace loader =>
      cases loader with
      | prepared loaded =>
          simp only [PacketResponseSource.step, PMF.mem_support_pure_iff] at h
          subst next
          simp only [size, frameSize, machineSize, ControllerExtent.frameExtent,
            ConfigurationEncoding.pc, ControllerExtent.controlExtent, Machine.ControllerExtent.machine,
            NativePacketService.Resources.size, NativePacketService.Resources.pc,
            NativePacketService.Resources.extent, increment]
          omega
      | _ =>
          simp only [PacketResponseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨after, ha, rfl⟩ := h
          have hb := NativePacketService.Resources.step_size [] _ after ha
          simp only [size, increment, Program.addressCap] at *
          omega

end CryptoOracle.Interactive.PacketResponseGrowth
