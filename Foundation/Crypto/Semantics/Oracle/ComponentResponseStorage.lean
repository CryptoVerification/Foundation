import Foundation.Crypto.Semantics.Oracle.ComponentResponseCallback
import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded
import Foundation.Crypto.Semantics.ResourceEnvelope

/-! Storage for the complete component-to-caller callback, including the
fixed suspended-caller environment even after an active source copy exists.
The abstract component supplies local growth and handoff resource laws. -/
namespace CryptoOracle.Interactive.ComponentResponseStorage
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentCells componentExtent : Component → Nat)
    (stateSize : State → Nat) (savedSize : Saved → Nat)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

def metadataCells : Nat :=
  caller.tapeCells + stateSize state + SourceStorage.traceCells trace + request.length

def cells : ComponentResponseCallback.Control Component State Saved → Nat
  | .processing component => metadataCells stateSize caller state trace request + componentCells component
  | .delivering frame => metadataCells stateSize caller state trace request +
      ControllerStorage.callbackCells stateSize frame.1 + savedSize frame.2

def extent : ComponentResponseCallback.Control Component State Saved → Nat
  | .processing component => max (ControllerExtent.metadataExtent stateSize caller state trace request) (componentExtent component)
  | .delivering frame => max (ControllerExtent.metadataExtent stateSize caller state trace request)
      (max (ControllerExtent.callbackExtent stateSize frame.1) (savedSize frame.2))

theorem metadata_bound (cap : Nat)
    (h : ControllerExtent.metadataExtent stateSize caller state trace request ≤ cap) :
    metadataCells stateSize caller state trace request ≤ 2 * cap ^ 2 + 4 * cap := by
  have ht := ControllerExtent.trace_cells trace
  have hq : (ControllerExtent.traceExtent trace) ^ 2 ≤ cap ^ 2 :=
    Nat.pow_le_pow_left (by unfold ControllerExtent.metadataExtent at h; omega) 2
  have hc : caller.tapeCells ≤ 2 * cap := by
    simp only [ControllerExtent.metadataExtent, Machine.ControllerExtent.machine,
      Machine.Configuration.tapeCells] at *
    omega
  have hs : stateSize state ≤ cap := by unfold ControllerExtent.metadataExtent at h; omega
  have hr : request.length ≤ cap := by unfold ControllerExtent.metadataExtent at h; omega
  simp only [metadataCells]
  nlinarith

variable (coefficient constant : Nat)
    (hComponent : ∀ component, componentCells component ≤ coefficient * componentExtent component + constant)

include hComponent in
theorem cells_bound (c : ComponentResponseCallback.Control Component State Saved) :
    cells componentCells stateSize savedSize caller state trace request c ≤
      4 * (extent componentExtent stateSize savedSize caller state trace request c) ^ 2 +
        (coefficient + 10) * extent componentExtent stateSize savedSize caller state trace request c + constant + 1 := by
  cases c with
  | processing component =>
      have hm := metadata_bound stateSize caller state trace request
        (extent componentExtent stateSize savedSize caller state trace request (.processing component))
        (by simp only [extent]; omega)
      have hc := hComponent component
      have he : componentExtent component ≤ extent componentExtent stateSize savedSize caller state trace request (.processing component) := by
        simp only [extent]; omega
      have hs := Nat.mul_le_mul_left coefficient he
      simp only [cells] at ⊢
      nlinarith
  | delivering frame =>
      have hm := metadata_bound stateSize caller state trace request
        (extent componentExtent stateSize savedSize caller state trace request (.delivering frame))
        (by simp only [extent]; omega)
      have hc := ControllerExtent.callback_cells stateSize frame.1
      have he : ControllerExtent.callbackExtent stateSize frame.1 ≤
          extent componentExtent stateSize savedSize caller state trace request (.delivering frame) := by
        simp only [extent]; omega
      have hs : savedSize frame.2 ≤ extent componentExtent stateSize savedSize caller state trace request (.delivering frame) := by
        simp only [extent]; omega
      have hq := Nat.pow_le_pow_left he 2
      simp only [cells] at ⊢
      nlinarith

variable (componentStep : Component → PMF Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (componentIncrement stateIncrement responseCap : Nat)
    (hStep : ∀ start target, target ∈ (componentStep start).support →
      componentExtent target ≤ componentExtent start + componentIncrement)
    (hReady : ∀ component machine saved, ready component = some (machine, saved) →
      Machine.ControllerExtent.machine machine ≤ componentExtent component ∧ savedSize saved ≤ componentExtent component)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hStep hReady hOracle in
theorem extent_step (start target : ComponentResponseCallback.Control Component State Saved)
    (h : target ∈ (ComponentResponseCallback.step componentStep ready native code oracle caller state trace request start).support) :
    extent componentExtent stateSize savedSize caller state trace request target ≤
      extent componentExtent stateSize savedSize caller state trace request start +
        (componentIncrement + stateIncrement + responseCap + 2) := by
  cases start with
  | processing component =>
      cases hr : ready component with
      | none =>
          simp only [ComponentResponseCallback.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := hStep component next hn
          simp only [extent]
          omega
      | some frame =>
          rcases frame with ⟨machine, saved⟩
          simp only [ComponentResponseCallback.step, hr, PMF.mem_support_pure_iff] at h
          subst target
          obtain ⟨hm, hs⟩ := hReady component machine saved hr
          simp only [extent, ControllerExtent.callbackExtent, Machine.ControllerExtent.exportExtent]
          omega
  | delivering frame =>
      rcases frame with ⟨callback, retained⟩
      simp only [ComponentResponseCallback.step, framedStep, PMF.map_comp, Function.comp_def,
        PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hb := ControllerExtent.callback_step stateSize native code oracle stateIncrement responseCap hOracle
        caller state trace request callback next hn
      simp only [extent]
      omega

def bound (initialExtent horizon componentIncrement stateIncrement responseCap coefficient constant : Nat) : Nat :=
  let e := initialExtent + horizon * (componentIncrement + stateIncrement + responseCap + 2)
  4 * e ^ 2 + (coefficient + 10) * e + constant + 1

include hComponent hStep hReady hOracle in
/-- Applies to all execution prefixes, including continued caller steps. -/
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : ComponentResponseCallback.Control Component State Saved)
    (hTarget : target ∈ (TimedExecution.eval
      (ComponentResponseCallback.step componentStep ready native code oracle caller state trace request) elapsed start).support) :
    cells componentCells stateSize savedSize caller state trace request target ≤
      bound (extent componentExtent stateSize savedSize caller state trace request start)
        horizon componentIncrement stateIncrement responseCap coefficient constant := by
  have he := ResourceGrowth.prefix_bound
    (ComponentResponseCallback.step componentStep ready native code oracle caller state trace request)
    (extent componentExtent stateSize savedSize caller state trace request)
    (componentIncrement + stateIncrement + responseCap + 2)
    (extent_step componentExtent stateSize savedSize caller state trace request componentStep ready native code oracle
      componentIncrement stateIncrement responseCap hStep hReady hOracle)
    horizon elapsed hElapsed start target hTarget
  have hc := cells_bound componentCells componentExtent stateSize savedSize caller state trace request coefficient constant hComponent target
  have hq := Nat.pow_le_pow_left he 2
  have hl := Nat.mul_le_mul_left (coefficient + 10) he
  dsimp only [bound]
  omega

theorem bound_polynomial {initialExtent horizon componentIncrement stateIncrement responseCap : Nat → Nat}
    (hExtent : PolynomiallyBounded initialExtent) (hTime : PolynomiallyBounded horizon)
    (hComponent : PolynomiallyBounded componentIncrement) (hState : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) (coefficient constant : Nat) :
    PolynomiallyBounded (fun n => bound (initialExtent n) (horizon n) (componentIncrement n)
      (stateIncrement n) (responseCap n) coefficient constant) := by
  have he := hExtent.add (hTime.mul (((hComponent.add hState).add hResponse).add (PolynomiallyBounded.const 2)))
  have hb := ((((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const (coefficient + 10)).mul he)).add (PolynomiallyBounded.const constant)).add (PolynomiallyBounded.const 1)
  simpa only [bound, pow_two] using hb

end CryptoOracle.Interactive.ComponentResponseStorage
