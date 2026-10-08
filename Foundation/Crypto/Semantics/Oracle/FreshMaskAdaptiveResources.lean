import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveExecution
import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoopResources
import Foundation.Crypto.Semantics.Oracle.PacketResponseResources

/-! Whole-prefix storage of the actual repeated native masking execution.
Both source and component code, caller and component tapes, raw buffers,
explicit blanks, retained state and full trace are included. External-state
codec/growth obligations remain explicit, with a closed-oracle instance. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveResources
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

abbrev componentSize := NativePacketService.Resources.size

def unitEncoding : FiniteBitEncoding Unit := ⟨fun _ => [], fun _ => some (), by intro unitArg; cases unitArg; rfl⟩

noncomputable def native := FreshMaskResponse.component.procedure.code

private theorem component_growth (start next : NativePacketService.Control)
    (h : next ∈ (FreshMaskCallerService.componentStep start).support) :
    componentSize next ≤ componentSize start + (native.addressCap + 1) :=
  NativePacketService.Resources.step_size native start next h

private theorem begin_growth (retained : Unit) (request : List Bool) :
    componentSize (FreshMaskCallerService.begin retained request) ≤ max 0 request.length + 1 := by
  simp [componentSize, FreshMaskCallerService.begin, NativePacketService.Resources.size,
    NativePacketService.Resources.pc, NativePacketService.Resources.extent, Tape.cells]

private theorem ready_growth (component : NativePacketService.Control) (retained : Unit) (packet : List Bool)
    (h : FreshMaskCallerService.ready component = some (retained, packet)) :
    0 ≤ componentSize component + 0 ∧ packet.length ≤ componentSize component + 0 := by
  cases retained
  cases component <;> simp_all [FreshMaskCallerService.ready]
  rename_i component
  cases component <;> simp_all [FreshMaskCallerService.ready]
  simp [componentSize, NativePacketService.Resources.size, NativePacketService.Resources.pc,
    NativePacketService.Resources.extent, ControllerExtent.exportExtent]

noncomputable def increment (stateIncrement responseCap : Nat) : Nat :=
  PacketResponseGrowth.increment AdaptiveBitstringLoop.code (native.addressCap + 1) 1 0 stateIncrement responseCap

noncomputable def bitBound (stateSize stateIncrement responseCap rounds width : Nat) : Nat :=
  PacketResponseEncoding.bitBound AdaptiveBitstringLoop.code native 76 60
    (stateSize + rounds + width + 2) (FreshMaskAdaptiveExecution.timeBound rounds width)
    (increment stateIncrement responseCap)

variable {State : Type u}

private theorem initial_size (stateSize : State → Nat) (state : State) (rounds : Nat) (request : List Bool) :
    PacketResponseGrowth.size componentSize stateSize (fun _ : Unit => 0)
      (.source () (AdaptiveBitstringLoop.frame state rounds [] request [])) ≤
        stateSize state + rounds + request.length + 2 := by
  have he := AdaptiveBitstringLoop.initial_extent stateSize state rounds request
  simp only [PacketResponseGrowth.size, PacketResponseGrowth.frameSize,
    AdaptiveBitstringLoop.frame, ConfigurationEncoding.pc, AdaptiveBitstringLoop.machine] at he ⊢
  omega

theorem peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (state : State) (rounds : Nat) (request : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ FreshMaskAdaptiveExecution.timeBound rounds request.length)
    (target : PacketResponseSource.Control NativePacketService.Control State Unit)
    (hTarget : target ∈ (TimedExecution.eval (FreshMaskAdaptiveRound.runtime oracle).step elapsed
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds [] request []))).support) :
    ((PacketResponseEncoding.completeEncoding NativePacketService.Resources.encoding E unitEncoding).encode
      (AdaptiveBitstringLoop.code, native, target)).length ≤
      bitBound (stateSize state) stateIncrement responseCap rounds request.length := by
  have hp := PacketResponseResources.peak NativePacketService.Resources.encoding E unitEncoding
    FreshMaskCallerService.componentStep FreshMaskCallerService.begin FreshMaskCallerService.ready
    AdaptiveBitstringLoop.code oracle native componentSize stateSize (fun _ : Unit => 0)
    76 60 (native.addressCap + 1) 1 0 stateIncrement responseCap
    NativePacketService.Resources.encoding_length hState (fun _ => Nat.le_refl 0)
    component_growth begin_growth ready_growth hOracle
    (.source () (AdaptiveBitstringLoop.frame state rounds [] request [])) target
    (FreshMaskAdaptiveExecution.timeBound rounds request.length) elapsed hElapsed hTarget
  exact hp.trans (PacketResponseEncoding.bitBound_mono AdaptiveBitstringLoop.code native 76 60
    (initial_size stateSize state rounds request) (Nat.le_refl _) (Nat.le_refl _))

noncomputable def idleOracle : BitOracle State := fun state _ => PMF.pure (state, [])

/-- No boundedness premise about an external response source is needed
when the experiment is closed; all ciphertexts are computed internally. -/
theorem peak_closed (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (state : State) (rounds : Nat) (request : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ FreshMaskAdaptiveExecution.timeBound rounds request.length)
    (target : PacketResponseSource.Control NativePacketService.Control State Unit)
    (hTarget : target ∈ (TimedExecution.eval (FreshMaskAdaptiveRound.runtime (idleOracle : BitOracle State)).step elapsed
      ((FreshMaskAdaptiveRound.runtime (idleOracle : BitOracle State)).embed ()
        (AdaptiveBitstringLoop.frame state rounds [] request []))).support) :
    ((PacketResponseEncoding.completeEncoding NativePacketService.Resources.encoding E unitEncoding).encode
      (AdaptiveBitstringLoop.code, native, target)).length ≤ bitBound (stateSize state) 0 0 rounds request.length :=
  peak E stateSize hState idleOracle 0 0 (by
    intro state request result hResult
    rw [idleOracle, PMF.mem_support_pure_iff] at hResult
    subst result
    simp) state rounds request elapsed hElapsed target hTarget

theorem space_polynomial {stateSize stateIncrement responseCap rounds width : Nat → Nat}
    (hState : PolynomiallyBounded stateSize) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) (hRounds : PolynomiallyBounded rounds)
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => bitBound (stateSize n) (stateIncrement n) (responseCap n) (rounds n) (width n)) := by
  apply PacketResponseResources.bitBound_polynomial AdaptiveBitstringLoop.code native 76 60
  · exact ((hState.add hRounds).add hWidth).add (PolynomiallyBounded.const 2)
  · exact FreshMaskAdaptiveExecution.time_polynomial hRounds hWidth
  · exact (((((PolynomiallyBounded.const (EncodedStorage.addressCap AdaptiveBitstringLoop.code)).add
      (PolynomiallyBounded.const (native.addressCap + 1))).add (PolynomiallyBounded.const 1)).add
      (PolynomiallyBounded.const 0)).add hIncrement).add hResponse |>.add (PolynomiallyBounded.const 3)

end CryptoOracle.Interactive.FreshMaskAdaptiveResources
