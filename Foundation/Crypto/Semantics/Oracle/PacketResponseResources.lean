import Foundation.Crypto.Semantics.Oracle.PacketResponseEncoding

/-! Whole-prefix representation bounds for packet caller runtimes. Local
component/launch/return obligations are explicit and reusable across schemes.
All actual states and the supplied source/component code blocks are encoded. -/
namespace CryptoOracle.Interactive.PacketResponseResources
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}

theorem peak_with_bounds (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved)
    (componentStep : Component → PMF Component) (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool)) (code : Code) (oracle : BitOracle State) (native : Machine.Program)
    (componentSize : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat)
    (componentBound savedBound : Nat → Nat)
    (hComponentMono : Monotone componentBound) (hSavedMono : Monotone savedBound)
    (componentIncrement beginIncrement readyIncrement stateIncrement responseCap : Nat)
    (hComponentEncoding : ∀ component, (EC.encode component).length ≤ componentBound (componentSize component))
    (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (hSaved : ∀ retained, (EK.encode retained).length ≤ savedBound (savedSize retained))
    (hComponent : ∀ start next, next ∈ (componentStep start).support → componentSize next ≤ componentSize start + componentIncrement)
    (hBegin : ∀ retained request, componentSize (begin retained request) ≤ max (savedSize retained) request.length + beginIncrement)
    (hReady : ∀ component retained packet, ready component = some (retained, packet) →
      savedSize retained ≤ componentSize component + readyIncrement ∧ packet.length ≤ componentSize component + readyIncrement)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start target : PacketResponseSource.Control Component State Saved) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (hTarget : target ∈ (TimedExecution.eval (PacketResponseSource.step componentStep begin ready code oracle) elapsed start).support) :
    ((PacketResponseEncoding.completeEncoding EC ES EK).encode (code, native, target)).length ≤
      PacketResponseEncoding.bitBoundWith code native componentBound savedBound
        (PacketResponseGrowth.size componentSize stateSize savedSize start) horizon
        (PacketResponseGrowth.increment code componentIncrement beginIncrement readyIncrement stateIncrement responseCap) := by
  have hs := ResourceGrowth.prefix_bound (PacketResponseSource.step componentStep begin ready code oracle)
    (PacketResponseGrowth.size componentSize stateSize savedSize)
    (PacketResponseGrowth.increment code componentIncrement beginIncrement readyIncrement stateIncrement responseCap)
    (PacketResponseGrowth.step_bound componentStep begin ready code oracle componentSize stateSize savedSize
      componentIncrement beginIncrement readyIncrement stateIncrement responseCap hComponent hBegin hReady hOracle)
    horizon elapsed hElapsed start target hTarget
  have he := PacketResponseEncoding.length_cap_with_bounds EC ES EK componentSize stateSize savedSize
    componentBound savedBound hComponentMono hSavedMono hComponentEncoding hState hSaved target _ hs
  simp only [PacketResponseEncoding.completeEncoding, FiniteBitEncoding.prod_encode_length]
  unfold PacketResponseEncoding.bitBoundWith
  omega

theorem peak (EC : FiniteBitEncoding Component) (ES : FiniteBitEncoding State) (EK : FiniteBitEncoding Saved)
    (componentStep : Component → PMF Component) (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool)) (code : Code) (oracle : BitOracle State) (native : Machine.Program)
    (componentSize : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat)
    (factor constant componentIncrement beginIncrement readyIncrement stateIncrement responseCap : Nat)
    (hComponentEncoding : ∀ component, (EC.encode component).length ≤ factor * componentSize component + constant)
    (hState : ∀ state, (ES.encode state).length ≤ stateSize state)
    (hSaved : ∀ retained, (EK.encode retained).length ≤ savedSize retained)
    (hComponent : ∀ start next, next ∈ (componentStep start).support → componentSize next ≤ componentSize start + componentIncrement)
    (hBegin : ∀ retained request, componentSize (begin retained request) ≤ max (savedSize retained) request.length + beginIncrement)
    (hReady : ∀ component retained packet, ready component = some (retained, packet) →
      savedSize retained ≤ componentSize component + readyIncrement ∧ packet.length ≤ componentSize component + readyIncrement)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start target : PacketResponseSource.Control Component State Saved) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (hTarget : target ∈ (TimedExecution.eval (PacketResponseSource.step componentStep begin ready code oracle) elapsed start).support) :
    ((PacketResponseEncoding.completeEncoding EC ES EK).encode (code, native, target)).length ≤
      PacketResponseEncoding.bitBound code native factor constant
        (PacketResponseGrowth.size componentSize stateSize savedSize start) horizon
        (PacketResponseGrowth.increment code componentIncrement beginIncrement readyIncrement stateIncrement responseCap) := by
  have he := peak_with_bounds EC ES EK componentStep begin ready code oracle native
    componentSize stateSize savedSize (fun size => factor * size + constant) id
    (by intro a b h; exact Nat.add_le_add_right (Nat.mul_le_mul_left factor h) constant)
    (by intro a b h; exact h)
    componentIncrement beginIncrement readyIncrement stateIncrement responseCap
    hComponentEncoding hState hSaved hComponent hBegin hReady hOracle
    start target horizon elapsed hElapsed hTarget
  dsimp only [PacketResponseEncoding.bitBoundWith, PacketResponseEncoding.boundWith, id_eq] at he
  unfold PacketResponseEncoding.bitBound PacketResponseEncoding.bound
  rw [Nat.add_mul]
  omega

theorem bitBound_polynomial (code : Code) (native : Machine.Program) (factor constant : Nat)
    {initialSize horizon increment : Nat → Nat} (hSize : PolynomiallyBounded initialSize)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded increment) :
    PolynomiallyBounded (fun n => PacketResponseEncoding.bitBound code native factor constant
      (initialSize n) (horizon n) (increment n)) := by
  have hc := hSize.add (hTime.mul hIncrement)
  have hb := ((((PolynomiallyBounded.const 200).mul (hc.pow 2)).add
    ((PolynomiallyBounded.const (1000 + factor)).mul hc)).add (PolynomiallyBounded.const constant)).add
      (PolynomiallyBounded.const 500)
  exact (PolynomiallyBounded.const (2 * (StructuredCodeStorage.codeEncoding.encode code).length +
    2 * (StructuredCodeEncoding.program.encode native).length + 2)).add hb

end CryptoOracle.Interactive.PacketResponseResources
