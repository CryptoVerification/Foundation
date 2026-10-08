import Foundation.Crypto.Semantics.Oracle.PacketResponseGrowth

/-! Faithful storage of every packet caller phase. Private retained data,
source tapes, component data, all loaders, control addresses and complete
transcripts are represented. Codecs are storage witnesses, not free actions. -/
namespace CryptoOracle.Interactive.PacketResponseEncoding
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {Component : Type u} {State : Type v} {Saved : Type w}

def fields (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved) :=
  (EK.prod (ConfigurationEncoding.frame ES)).sum
    ((ConfigurationEncoding.native.prod (ES.prod (ConfigurationEncoding.trace.prod (ConfigurationEncoding.bits.prod EC)))).sum
      (EK.prod (ConfigurationEncoding.native.prod (ES.prod (ConfigurationEncoding.trace.prod NativePacketService.Resources.encoding)))))

def encoding (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved) :
    FiniteBitEncoding (PacketResponseSource.Control Component State Saved) where
  encode := fun outer => (fields EC ES EK).encode (match outer with
    | .source retained frame => .inl (retained, frame)
    | .processing caller state trace request component => .inr (.inl (caller, state, trace, request, component))
    | .returning retained caller state trace loader => .inr (.inr (retained, caller, state, trace, loader)))
  decode := fun raw => ((fields EC ES EK).decode raw).map fun outer => match outer with
    | .inl (retained, frame) => .source retained frame
    | .inr (.inl (caller, state, trace, request, component)) => .processing caller state trace request component
    | .inr (.inr (retained, caller, state, trace, loader)) => .returning retained caller state trace loader
  decode_encode := by intro outer; cases outer <;> simp [(fields EC ES EK).decode_encode]

private theorem native_cap (machine : Machine.Configuration) (cap : Nat)
    (h : PacketResponseGrowth.machineSize machine ≤ cap) :
    (ConfigurationEncoding.native.encode machine).length ≤ 38 * cap + 14 := by
  change (Machine.ConfigurationEncoding.configuration.encode machine).length ≤ _
  have hm := Machine.ConfigurationEncoding.configuration_length_le machine
  have hc := Machine.ControllerExtent.machine_cells machine
  simp only [PacketResponseGrowth.machineSize] at h
  omega

private theorem trace_cap (trace : List (List Bool × List Bool)) (cap : Nat)
    (h : ControllerExtent.traceExtent trace ≤ cap) :
    (ConfigurationEncoding.trace.encode trace).length ≤ 8 * cap ^ 2 + 4 * cap + 1 := by
  have he := ConfigurationEncoding.trace_length_le trace
  have hc := ControllerExtent.trace_cells trace
  have hl := ControllerExtent.trace_length trace
  have hq := Nat.pow_le_pow_left h 2
  omega

private theorem frame_cap (ES : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (ES.encode state).length ≤ stateSize state) (frame : Configuration State)
    (cap : Nat) (h : PacketResponseGrowth.frameSize stateSize frame ≤ cap) :
    ((ConfigurationEncoding.frame ES).encode frame).length ≤ 144 * cap ^ 2 + 372 * cap + 172 := by
  have he := ConfigurationEncoding.frame_extent_length_le ES stateSize hState frame
  have hb : ControllerExtent.frameExtent stateSize frame ≤ cap := by
    simp only [PacketResponseGrowth.frameSize] at h; omega
  have hp : ConfigurationEncoding.pc frame.control ≤ cap := by
    simp only [PacketResponseGrowth.frameSize] at h; omega
  have hq := Nat.pow_le_pow_left hb 2
  omega

def bound (factor constant cap : Nat) : Nat := 200 * cap ^ 2 + (1000 + factor) * cap + constant + 500

theorem length_cap (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved)
    (componentSize : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat)
    (factor constant : Nat)
    (hComponent : ∀ component, (EC.encode component).length ≤ factor * componentSize component + constant)
    (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (hSaved : ∀ retained, (EK.encode retained).length ≤ savedSize retained)
    (outer : PacketResponseSource.Control Component State Saved) (cap : Nat)
    (hCap : PacketResponseGrowth.size componentSize stateSize savedSize outer ≤ cap) :
    ((encoding EC ES EK).encode outer).length ≤ bound factor constant cap := by
  cases outer with
  | source retained frame =>
      have hs := hSaved retained
      have hf := frame_cap ES stateSize hState frame cap (by
        simp only [PacketResponseGrowth.size] at hCap; omega)
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length]
      simp only [PacketResponseGrowth.size] at hCap
      unfold bound
      rw [Nat.add_mul]
      omega
  | processing caller state trace request component =>
      simp only [PacketResponseGrowth.size] at hCap
      have hm := native_cap caller cap (by omega)
      have ht := trace_cap trace cap (by omega)
      have hs := hState state
      have hc := hComponent component
      have hMul := Nat.mul_le_mul_left factor (show componentSize component ≤ cap by omega)
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length,
        FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.bits, id_eq]
      unfold bound
      rw [Nat.add_mul]
      omega
  | returning retained caller state trace loader =>
      simp only [PacketResponseGrowth.size] at hCap
      have hm := native_cap caller cap (by omega)
      have ht := trace_cap trace cap (by omega)
      have hs := hState state
      have hk := hSaved retained
      have hl := NativePacketService.Resources.encoding_length loader
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length]
      unfold bound
      rw [Nat.add_mul]
      omega

def completeEncoding (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved) :
    FiniteBitEncoding (Code × Machine.Program × PacketResponseSource.Control Component State Saved) :=
  StructuredCodeStorage.codeEncoding.prod (StructuredCodeEncoding.program.prod (encoding EC ES EK))

def bitBound (code : Code) (native : Machine.Program) (factor constant initialSize horizon increment : Nat) : Nat :=
  2 * (StructuredCodeStorage.codeEncoding.encode code).length +
    2 * (StructuredCodeEncoding.program.encode native).length + 2 + bound factor constant (initialSize + horizon * increment)

theorem bitBound_mono (code : Code) (native : Machine.Program) (factor constant : Nat)
    {initial nextInitial time nextTime increment nextIncrement : Nat}
    (hInitial : initial ≤ nextInitial) (hTime : time ≤ nextTime) (hIncrement : increment ≤ nextIncrement) :
    bitBound code native factor constant initial time increment ≤
      bitBound code native factor constant nextInitial nextTime nextIncrement := by
  have hc := Nat.add_le_add hInitial (Nat.mul_le_mul hTime hIncrement)
  have hq := Nat.pow_le_pow_left hc 2
  have hl := Nat.mul_le_mul_left (1000 + factor) hc
  dsimp only [bitBound, bound]
  omega

end CryptoOracle.Interactive.PacketResponseEncoding
