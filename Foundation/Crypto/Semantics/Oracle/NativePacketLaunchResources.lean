import Foundation.Crypto.Semantics.Oracle.NativePacketLaunch
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentResources
import Foundation.Crypto.Semantics.Machine.NativePacketServiceResources

/-! Complete encoded storage throughout raw loading, native computation and
physical export. Fixed code, tape-role flag and prior history are included;
the history retained again inside a launched frame is counted separately. -/
namespace CryptoOracle.Interactive.NativePacketLaunch.Resources
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u}

def fields (E : FiniteBitEncoding State) :=
  (E.prod NativePacketService.Resources.encoding).sum (NativePacketComponent.Resources.encoding E)

def encoding (E : FiniteBitEncoding State) : FiniteBitEncoding (Control State) where
  encode := fun control => (fields E).encode (match control with
    | .preparing state loader => .inl (state, loader)
    | .running component => .inr component)
  decode := fun raw => ((fields E).decode raw).map fun value => match value with
    | .inl (state, loader) => .preparing state loader
    | .inr component => .running component
  decode_encode := by intro control; cases control <;> simp [(fields E).decode_encode]

def size (stateSize : State → Nat) (prior : List (List Bool × List Bool)) : Control State → Nat
  | .preparing state loader => max (stateSize state)
      (max (ControllerExtent.traceExtent prior) (NativePacketService.Resources.size loader))
  | .running component => max (ControllerExtent.traceExtent prior) (NativePacketComponent.Resources.size stateSize component)

theorem step_size (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (reverseRoles : Bool) (prior : List (List Bool × List Bool)) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : Control State) (support : next ∈ (step code oracle reverseRoles prior start).support) :
    size stateSize prior next ≤ size stateSize prior start + NativePacketComponent.Resources.increment code stateIncrement responseCap := by
  cases start with
  | preparing state loader =>
      have transport (loader : NativePacketService.Control)
          (same : step code oracle reverseRoles prior (.preparing state loader) =
            (NativePacketService.step [] loader).map (.preparing state))
          (support : next ∈ (step code oracle reverseRoles prior (.preparing state loader)).support) :
          size stateSize prior next ≤ size stateSize prior (.preparing state loader) +
            NativePacketComponent.Resources.increment code stateIncrement responseCap := by
        rw [same, PMF.mem_support_map_iff] at support
        obtain ⟨loaderNext, hn, rfl⟩ := support
        have h := NativePacketService.Resources.step_size [] loader loaderNext hn
        simp only [Program.addressCap] at h
        simp only [size, NativePacketComponent.Resources.increment]
        omega
      cases loader with
      | executing exporter =>
          cases exporter with
          | running machine =>
              simp only [step, PMF.mem_support_pure_iff] at support
              subst next
              cases reverseRoles <;>
                simp [size, NativePacketComponent.Resources.size, NativePacketComponent.Resources.frameSize,
                  handoffFrame, ConfigurationEncoding.pc, ControllerExtent.frameExtent, ControllerExtent.controlExtent,
                  NativePacketService.Resources.size, NativePacketService.Resources.pc, NativePacketService.Resources.extent,
                  ControllerEncoding.exportPc, Machine.ControllerExtent.exportExtent, Machine.ControllerExtent.machine,
                  Machine.Configuration.swapTapes, NativePacketComponent.Resources.increment] <;> omega
          | _ => apply transport _ rfl support
      | _ => apply transport _ rfl support
  | running component =>
      simp only [step, PMF.mem_support_map_iff] at support
      obtain ⟨componentNext, hn, rfl⟩ := support
      have h := NativePacketComponent.Resources.step_size stateSize code oracle stateIncrement responseCap hOracle component componentNext hn
      simp only [size]
      omega

theorem encoding_length (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (prior : List (List Bool × List Bool)) (control : Control State) :
    ((encoding E).encode control).length ≤
      1024 * (size stateSize prior control) ^ 2 + 2048 * size stateSize prior control + 1024 := by
  cases control with
  | preparing state loader =>
      have hs := hState state
      have hl := NativePacketService.Resources.encoding_length loader
      have hstate : stateSize state ≤ size stateSize prior (.preparing state loader) := by simp [size]
      have hloader : NativePacketService.Resources.size loader ≤ size stateSize prior (.preparing state loader) := by simp [size]
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length]
      omega
  | running component =>
      have hc := NativePacketComponent.Resources.encoding_length E stateSize hState component
      have hs : NativePacketComponent.Resources.size stateSize component ≤ size stateSize prior (.running component) := by simp [size]
      have hq := Nat.pow_le_pow_left hs 2
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length]
      omega

def completeEncoding (E : FiniteBitEncoding State) :
    FiniteBitEncoding (Code × Bool × List (List Bool × List Bool) × Control State) :=
  EncodedStorage.codeEncoding.prod (Machine.ConfigurationEncoding.bit.prod (ConfigurationEncoding.trace.prod (encoding E)))

def bitBound (code : Code) (prior : List (List Bool × List Bool))
    (initialSize horizon stateIncrement responseCap : Nat) : Nat :=
  let cap := initialSize + horizon * NativePacketComponent.Resources.increment code stateIncrement responseCap
  2 * (EncodedStorage.codeEncoding.encode code).length + 2 * (ConfigurationEncoding.trace.encode prior).length +
    1024 * cap ^ 2 + 2048 * cap + 1029

/-- Every supported intermediate state is counted, not only a final frame.
The fixed environment and each retained physical copy are encoded too. -/
theorem peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (reverseRoles : Bool) (prior : List (List Bool × List Bool))
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (start target : Control State)
    (support : target ∈ (TimedExecution.eval (step code oracle reverseRoles prior) elapsed start).support) :
    ((completeEncoding E).encode (code, reverseRoles, prior, target)).length ≤
      bitBound code prior (size stateSize prior start) horizon stateIncrement responseCap := by
  have hs := ResourceGrowth.prefix_bound (step code oracle reverseRoles prior) (size stateSize prior)
    (NativePacketComponent.Resources.increment code stateIncrement responseCap)
    (step_size stateSize code oracle reverseRoles prior stateIncrement responseCap hOracle)
    horizon elapsed within start target support
  have he := encoding_length E stateSize hState prior target
  have hq := Nat.pow_le_pow_left hs 2
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit, List.length_singleton]
  dsimp only [bitBound]
  omega

end CryptoOracle.Interactive.NativePacketLaunch.Resources
