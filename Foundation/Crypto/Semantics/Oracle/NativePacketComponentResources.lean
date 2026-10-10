import Foundation.Crypto.Semantics.Oracle.NativePacketComponent
import Foundation.Crypto.Semantics.Oracle.EncodedStorage
import Foundation.Crypto.Semantics.Machine.CellResponseExportResources
import Foundation.Crypto.Semantics.ResourceGrowth

/-! Complete physical storage during native computation and packet export.
The retained native frame and the exporter's actual tapes/lists are encoded
separately. No cell-equivalent smaller representative replaces either one. -/
namespace CryptoOracle.Interactive.NativePacketComponent.Resources
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u}

def fields (E : FiniteBitEncoding State) :=
  (ConfigurationEncoding.frame E).sum ((ConfigurationEncoding.frame E).prod ControllerEncoding.responseExport)

def encoding (E : FiniteBitEncoding State) : FiniteBitEncoding (Control State) where
  encode := fun control => (fields E).encode (match control with
    | .computing frame => .inl frame
    | .exporting frame exporter => .inr (frame, exporter))
  decode := fun raw => ((fields E).decode raw).map fun value => match value with
    | .inl frame => .computing frame
    | .inr (frame, exporter) => .exporting frame exporter
  decode_encode := by intro control; cases control <;> simp [(fields E).decode_encode]

def frameSize (stateSize : State → Nat) (frame : Configuration State) : Nat :=
  max 1 (max (ConfigurationEncoding.pc frame.control) (ControllerExtent.frameExtent stateSize frame))

def exportSize (exporter : ResponseExport.Control) : Nat :=
  max 1 (max (ControllerEncoding.exportPc exporter) (Machine.ControllerExtent.exportExtent exporter))

def size (stateSize : State → Nat) : Control State → Nat
  | .computing frame => frameSize stateSize frame
  | .exporting frame exporter => max (frameSize stateSize frame) (exportSize exporter)

def increment (code : Code) (stateIncrement responseCap : Nat) : Nat :=
  EncodedStorage.addressCap code + stateIncrement + responseCap + 3

theorem frame_step (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : Configuration State)
    (support : next ∈ (Reification.timedStep code oracle start).support) :
    frameSize stateSize next ≤ frameSize stateSize start + increment code stateIncrement responseCap := by
  have hp := EncodedStorage.pc_step code oracle start next support
  have he := ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle start next support
  simp only [frameSize, increment]
  omega

theorem step_size (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : Control State) (support : next ∈ (step code oracle start).support) :
    size stateSize next ≤ size stateSize start + increment code stateIncrement responseCap := by
  cases start with
  | computing frame =>
      by_cases ht : Reification.terminal frame.control = true
      · simp only [step, ht, ↓reduceIte] at support
        cases hc : frame.control <;>
          simp only [hc, PMF.mem_support_pure_iff] at support <;>
          subst next <;>
          simp [size, exportSize, frameSize, ControllerExtent.frameExtent, ControllerExtent.controlExtent,
            ConfigurationEncoding.pc, Machine.ControllerExtent.exportExtent, ControllerEncoding.exportPc,
            hc, increment]; omega
      · simp only [step, ht, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at support
        obtain ⟨frameNext, hn, rfl⟩ := support
        exact frame_step stateSize code oracle stateIncrement responseCap hOracle frame frameNext hn
  | exporting frame exporter =>
      simp only [step, PMF.mem_support_map_iff] at support
      obtain ⟨exporterNext, hn, rfl⟩ := support
      have he := CellResponseExport.Resources.step_extent [] exporter exporterNext hn
      have hp := CellResponseExport.Resources.step_pc [] exporter exporterNext hn
      simp only [Program.addressCap] at hp
      simp only [CellResponseExport.Resources.extent, CellResponseExport.Resources.pc] at he hp
      simp only [size, exportSize, increment]
      omega

theorem frame_encoding_length (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (frame : Configuration State) :
    ((ConfigurationEncoding.frame E).encode frame).length ≤
      144 * (frameSize stateSize frame) ^ 2 + 372 * frameSize stateSize frame + 172 := by
  have h := ConfigurationEncoding.frame_extent_length_le E stateSize hState frame
  have he : ControllerExtent.frameExtent stateSize frame ≤ frameSize stateSize frame := by simp [frameSize]
  have hp : ConfigurationEncoding.pc frame.control ≤ frameSize stateSize frame := by simp [frameSize]
  have hq := Nat.pow_le_pow_left he 2
  omega

theorem export_encoding_length (exporter : ResponseExport.Control) :
    (ControllerEncoding.responseExport.encode exporter).length ≤ 38 * exportSize exporter + 20 := by
  have h := ControllerEncoding.export_length_le exporter
  have he := Machine.ControllerExtent.export_cells exporter
  simp only [exportSize]
  omega

theorem encoding_length (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (control : Control State) :
    ((encoding E).encode control).length ≤ 512 * (size stateSize control) ^ 2 + 1024 * size stateSize control + 512 := by
  cases control with
  | computing frame =>
      have hf := frame_encoding_length E stateSize hState frame
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inl_length, size]
      omega
  | exporting frame exporter =>
      have hf := frame_encoding_length E stateSize hState frame
      have hx := export_encoding_length exporter
      have hframe : frameSize stateSize frame ≤ size stateSize (.exporting frame exporter) := by simp [size]
      have hexport : exportSize exporter ≤ size stateSize (.exporting frame exporter) := by simp [size]
      have hq := Nat.pow_le_pow_left hframe 2
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.prod_encode_length]
      omega

end CryptoOracle.Interactive.NativePacketComponent.Resources
