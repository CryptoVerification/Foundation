import Foundation.Constructions.Hash.NativePublicWorldService
import Foundation.Constructions.Hash.NativeRuntimeRawServiceResources

/-! Complete physical storage of both native windows and the continuing
caller, including both fixed code blocks, shared cache, prior environment,
window tag, retained frames and actual response loaders at every prefix. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n κ : Nat}

def nativeWorldSize (prior : List (List Bool × List Bool)) : NativeWorldComponent n κ → Nat
  | .inl component => NativePacketLaunch.Resources.size (tableSize n κ) prior component
  | .inr component => NativePacketLaunch.Resources.size (tableSize n κ) prior component

def nativeWorldEncoding : FiniteBitEncoding (NativeWorldComponent n κ) :=
  (NativePacketLaunch.Resources.encoding (tableEncoding n κ)).sum
    (NativePacketLaunch.Resources.encoding (tableEncoding n κ))

/-- One additional bit distinguishes the two actual window states. -/
def nativeWorldComponentBound (s : Nat) : Nat := runtimeRawComponentBound s + 1

theorem nativeWorldComponentBound_mono : Monotone nativeWorldComponentBound := by
  intro a b h
  exact Nat.add_le_add_right (runtimeRawComponentBound_mono h) 1

theorem nativeWorld_encoding_length (prior : List (List Bool × List Bool))
    (component : NativeWorldComponent n κ) :
    (nativeWorldEncoding.encode component).length ≤ nativeWorldComponentBound (nativeWorldSize prior component) := by
  cases component with
  | inl component =>
      have h := NativePacketLaunch.Resources.encoding_length (tableEncoding n κ) (tableSize n κ)
        (fun state => (tableEncoding_length _ _ state).le) prior component
      simpa only [nativeWorldEncoding, FiniteBitEncoding.sum_encode_inl_length,
        nativeWorldSize, nativeWorldComponentBound, runtimeRawComponentBound] using Nat.add_le_add_right h 1
  | inr component =>
      have h := NativePacketLaunch.Resources.encoding_length (tableEncoding n κ) (tableSize n κ)
        (fun state => (tableEncoding_length _ _ state).le) prior component
      simpa only [nativeWorldEncoding, FiniteBitEncoding.sum_encode_inr_length,
        nativeWorldSize, nativeWorldComponentBound, runtimeRawComponentBound] using Nat.add_le_add_right h 1

def nativeWorldIncrement (initial : Bits n) (terminal : Bits κ) : Nat :=
  max (NativePacketComponent.Resources.increment (runtimeLinkedHashCode initial.toList terminal.toList)
      (entryIncrement n κ) n)
    (NativePacketComponent.Resources.increment NativeCompressionCall.code (entryIncrement n κ) n)

theorem nativeWorld_step_size (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (start next : NativeWorldComponent n κ)
    (support : next ∈ (nativeWorldStep initial terminal prior start).support) :
    nativeWorldSize prior next ≤ nativeWorldSize prior start + nativeWorldIncrement initial terminal := by
  have growth : ∀ state request result, result ∈ (idealCompression n κ state request).support →
      tableSize n κ result.1 ≤ tableSize n κ state + entryIncrement n κ ∧ result.2.length ≤ n := by
    intro state request result hr
    have h := idealCompression_growth n κ state request result hr
    exact ⟨h.1, h.2.le⟩
  cases start with
  | inl component =>
      rw [nativeWorldStep, PMF.mem_support_map_iff] at support
      obtain ⟨successor, hs, rfl⟩ := support
      have h := NativePacketLaunch.Resources.step_size (tableSize n κ)
        (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior
        (entryIncrement n κ) n growth component successor hs
      simp only [nativeWorldSize, nativeWorldIncrement]
      omega
  | inr component =>
      rw [nativeWorldStep, PMF.mem_support_map_iff] at support
      obtain ⟨successor, hs, rfl⟩ := support
      have h := NativePacketLaunch.Resources.step_size (tableSize n κ)
        NativeCompressionCall.code (idealCompression n κ) false prior
        (entryIncrement n κ) n growth component successor hs
      simp only [nativeWorldSize, nativeWorldIncrement]
      omega

theorem nativeWorldBegin_size (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) (request : List Bool) :
    nativeWorldSize prior (nativeWorldBegin saved request) ≤
      max (runtimeRawSavedSize prior saved) request.length + 0 := by
  cases request with
  | nil => exact runtimeRawBegin_size prior saved []
  | cons bit rest =>
      have h := runtimeRawBegin_size prior saved rest
      cases bit <;> simp only [nativeWorldBegin, nativeWorldSize, List.length_cons] <;> omega

theorem nativeWorldReady_size (prior : List (List Bool × List Bool))
    (component : NativeWorldComponent n κ) (saved : Configuration (IdealTable n κ)) (packet : List Bool)
    (ready : nativeWorldReady component = some (saved, packet)) :
    runtimeRawSavedSize prior saved ≤ nativeWorldSize prior component + 0 ∧
      packet.length ≤ nativeWorldSize prior component + 0 := by
  cases component with
  | inl component => exact runtimeRawReady_size prior component saved packet ready
  | inr component => exact runtimeRawReady_size prior component saved packet ready

/-- Both fixed code blocks and the common flag/prior environment are stored
in every phase, including source execution without an active component. -/
def nativeWorldCallerEncoding {State : Type*} (ES : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (EncodedStorage.codeEncoding.prod (Machine.ConfigurationEncoding.bit.prod
    (ConfigurationEncoding.trace.prod (PacketResponseEncoding.completeEncoding
      (nativeWorldEncoding (n := n) (κ := κ)) ES (ConfigurationEncoding.frame (tableEncoding n κ))))))

/-- Every supported prefix of the actual two-window continuing controller.
No syntax, termination, table freshness or host-code efficiency is assumed. -/
theorem nativeWorldCaller_encoded_peak {State : Type*} (ES : FiniteBitEncoding State)
    (stateSize : State → Nat) (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (callerCode : Code) (callerOracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (callerOracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start target : PacketResponseSource.Control (NativeWorldComponent n κ) State (Configuration (IdealTable n κ)))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon)
    (support : target ∈ (TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle)
      elapsed start).support) :
    ((nativeWorldCallerEncoding (n := n) (κ := κ) ES).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, NativeCompressionCall.code, false, prior,
        callerCode, [], target)).length ≤
    2 * (EncodedStorage.codeEncoding.encode (runtimeLinkedHashCode initial.toList terminal.toList)).length +
      2 * (EncodedStorage.codeEncoding.encode NativeCompressionCall.code).length +
      2 * (ConfigurationEncoding.trace.encode prior).length + 6 +
      PacketResponseEncoding.bitBoundWith callerCode [] nativeWorldComponentBound runtimeRawSavedBound
        (PacketResponseGrowth.size (nativeWorldSize prior) stateSize (runtimeRawSavedSize prior) start) horizon
        (PacketResponseGrowth.increment callerCode (nativeWorldIncrement initial terminal) 0 0 stateIncrement responseCap) := by
  have he := PacketResponseResources.peak_with_bounds nativeWorldEncoding ES
    (ConfigurationEncoding.frame (tableEncoding n κ))
    (nativeWorldStep initial terminal prior) nativeWorldBegin nativeWorldReady callerCode callerOracle []
    (nativeWorldSize prior) stateSize (runtimeRawSavedSize prior)
    nativeWorldComponentBound runtimeRawSavedBound nativeWorldComponentBound_mono runtimeRawSavedBound_mono
    (nativeWorldIncrement initial terminal) 0 0 stateIncrement responseCap
    (nativeWorld_encoding_length prior) hState (runtimeRawSaved_encoding prior)
    (nativeWorld_step_size initial terminal prior) (nativeWorldBegin_size prior) (nativeWorldReady_size prior)
    hOracle start target horizon elapsed within support
  simp only [nativeWorldCallerEncoding, FiniteBitEncoding.prod_encode_length,
    Machine.ConfigurationEncoding.bit, List.length_singleton]
  omega

/-- Apply the complete peak bound directly to the existing service's
costed output, using its operational reachability and certified budget. -/
theorem nativeWorldService_encoded_peak {State : Type*} (ES : FiniteBitEncoding State)
    (stateSize : State → Nat) (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (callerCode : Code) (callerOracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (callerOracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (table : CompressionTable (Bits κ) (Bits n)) (request : WorldInput (Bits κ) (Bits n))
    (result : (Configuration (IdealTable n κ) × Configuration State) × Nat)
    (support : result ∈ ((nativeWorldService initial terminal prior callerCode callerOracle
      caller state trace table request).costed ()).support) :
    ((nativeWorldCallerEncoding (n := n) (κ := κ) ES).encode
      (runtimeLinkedHashCode initial.toList terminal.toList, NativeCompressionCall.code, false, prior,
        callerCode, [], PacketResponseSource.Control.source result.1.1 result.1.2)).length ≤
    2 * (EncodedStorage.codeEncoding.encode (runtimeLinkedHashCode initial.toList terminal.toList)).length +
      2 * (EncodedStorage.codeEncoding.encode NativeCompressionCall.code).length +
      2 * (ConfigurationEncoding.trace.encode prior).length + 6 +
      PacketResponseEncoding.bitBoundWith callerCode [] nativeWorldComponentBound runtimeRawSavedBound
        (PacketResponseGrowth.size (nativeWorldSize prior) stateSize (runtimeRawSavedSize prior)
          ((nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).entry ()))
        (nativeWorldBudget request + (3 * n + 4))
        (PacketResponseGrowth.increment callerCode (nativeWorldIncrement initial terminal) 0 0 stateIncrement responseCap) := by
  have reached := nativeWorldService_operational initial terminal prior callerCode callerOracle
    caller state trace table request () result support
  rw [nativeWorldService_exit] at reached
  have bounded := (nativeWorldService initial terminal prior callerCode callerOracle
    caller state trace table request).bounded () result support
  rw [nativeWorldService_budget] at bounded
  exact nativeWorldCaller_encoded_peak ES stateSize hState initial terminal prior callerCode callerOracle
    stateIncrement responseCap hOracle _ _ _ result.2 bounded reached

end Foundation.Hash.Native
