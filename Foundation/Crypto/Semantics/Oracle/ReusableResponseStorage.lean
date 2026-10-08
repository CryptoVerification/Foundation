import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.Oracle.ComponentResponseStorage

/-! Whole-runtime storage across arbitrary repeated requests. Component
handoffs preserve extent even when metadata and payload copies coexist. -/
namespace CryptoOracle.Interactive.ReusableResponseStorage
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentCells componentExtent : Component → Nat) (stateSize : State → Nat) (savedSize : Saved → Nat)

def cells : ReusableResponseSource.Control Component State Saved → Nat
  | .source retained frame => savedSize retained + SourceStorage.cells stateSize frame
  | .processing caller state trace request component =>
      ComponentResponseStorage.metadataCells stateSize caller state trace request + componentCells component
  | .calling caller state trace request callback retained =>
      ComponentResponseStorage.metadataCells stateSize caller state trace request +
        ControllerStorage.callbackCells stateSize callback + savedSize retained

def extent : ReusableResponseSource.Control Component State Saved → Nat
  | .source retained frame => max (savedSize retained) (ControllerExtent.frameExtent stateSize frame)
  | .processing caller state trace request component =>
      max (ControllerExtent.metadataExtent stateSize caller state trace request) (componentExtent component)
  | .calling caller state trace request callback retained =>
      max (ControllerExtent.metadataExtent stateSize caller state trace request)
        (max (ControllerExtent.callbackExtent stateSize callback) (savedSize retained))

variable (coefficient constant : Nat)
    (hComponent : ∀ c, componentCells c ≤ coefficient * componentExtent c + constant)

include hComponent in
theorem cells_bound (c : ReusableResponseSource.Control Component State Saved) :
    cells componentCells stateSize savedSize c ≤
      4 * (extent componentExtent stateSize savedSize c) ^ 2 +
        (coefficient + 10) * extent componentExtent stateSize savedSize c + constant + 1 := by
  cases c with
  | source retained frame =>
      have hc := ControllerExtent.frame_cells stateSize frame
      have he : ControllerExtent.frameExtent stateSize frame ≤ extent componentExtent stateSize savedSize (.source retained frame) := by
        simp only [extent]; omega
      have hs : savedSize retained ≤ extent componentExtent stateSize savedSize (.source retained frame) := by
        simp only [extent]; omega
      have hq := Nat.pow_le_pow_left he 2
      simp only [cells]
      nlinarith
  | processing caller state trace request component =>
      exact ComponentResponseStorage.cells_bound componentCells componentExtent stateSize savedSize
        caller state trace request coefficient constant hComponent (.processing component)
  | calling caller state trace request callback retained =>
      exact ComponentResponseStorage.cells_bound componentCells componentExtent stateSize savedSize
        caller state trace request coefficient constant hComponent (.delivering (callback, retained))

variable (componentStep : Component → PMF Component) (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (beginIncrement componentIncrement stateIncrement responseCap : Nat)
    (hBegin : ∀ retained request, componentExtent (begin retained request) ≤
      max (savedSize retained) request.length + beginIncrement)
    (hStep : ∀ start target, target ∈ (componentStep start).support →
      componentExtent target ≤ componentExtent start + componentIncrement)
    (hReady : ∀ component machine saved, ready component = some (machine, saved) →
      Machine.ControllerExtent.machine machine ≤ componentExtent component ∧ savedSize saved ≤ componentExtent component)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hBegin hStep hReady hOracle in
theorem extent_step (start target : ReusableResponseSource.Control Component State Saved)
    (h : target ∈ (ReusableResponseSource.step componentStep begin ready native code oracle start).support) :
    extent componentExtent stateSize savedSize target ≤ extent componentExtent stateSize savedSize start +
      (beginIncrement + componentIncrement + stateIncrement + responseCap + 2) := by
  cases start with
  | source retained frame =>
      rcases frame with ⟨state, control, trace⟩
      cases control with
      | awaiting caller request =>
          simp only [ReusableResponseSource.step, PMF.mem_support_pure_iff] at h
          subst target
          have hb := hBegin retained request
          simp only [extent, ControllerExtent.frameExtent, ControllerExtent.controlExtent,
            ControllerExtent.metadataExtent]
          omega
      | _ =>
          simp only [ReusableResponseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle _ next hn
          simp only [extent]
          omega
  | processing caller state trace request component =>
      cases hr : ready component with
      | none =>
          simp only [ReusableResponseSource.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := hStep component next hn
          simp only [extent]
          omega
      | some frame =>
          rcases frame with ⟨machine, retained⟩
          simp only [ReusableResponseSource.step, hr, PMF.mem_support_pure_iff] at h
          subst target
          obtain ⟨hm, hs⟩ := hReady component machine retained hr
          simp only [extent, ControllerExtent.callbackExtent, Machine.ControllerExtent.exportExtent]
          omega
  | calling caller state trace request callback retained =>
      cases callback with
      | responding component =>
          simp only [ReusableResponseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := ControllerExtent.callback_step stateSize native code oracle stateIncrement responseCap hOracle
            caller state trace request (.responding component) next hn
          simp only [extent]
          omega
      | source frame =>
          rcases frame with ⟨nextState, control, nextTrace⟩
          cases control with
          | running machine =>
              simp only [ReusableResponseSource.step, PMF.mem_support_pure_iff] at h
              subst target
              simp only [extent, ControllerExtent.callbackExtent]
              omega
          | _ =>
              simp only [ReusableResponseSource.step, NativeCallback.step, PMF.map_comp, Function.comp_def,
                PMF.mem_support_map_iff] at h
              obtain ⟨next, hn, rfl⟩ := h
              have hb := ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle _ next hn
              simp only [extent, ControllerExtent.callbackExtent]
              omega

def bound (initialExtent horizon beginIncrement componentIncrement stateIncrement responseCap coefficient constant : Nat) :=
  let e := initialExtent + horizon * (beginIncrement + componentIncrement + stateIncrement + responseCap + 2)
  4 * e ^ 2 + (coefficient + 10) * e + constant + 1

include hComponent hBegin hStep hReady hOracle in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : ReusableResponseSource.Control Component State Saved)
    (hTarget : target ∈ (TimedExecution.eval
      (ReusableResponseSource.step componentStep begin ready native code oracle) elapsed start).support) :
    cells componentCells stateSize savedSize target ≤
      bound (extent componentExtent stateSize savedSize start) horizon beginIncrement componentIncrement
        stateIncrement responseCap coefficient constant := by
  have he := ResourceGrowth.prefix_bound (ReusableResponseSource.step componentStep begin ready native code oracle)
    (extent componentExtent stateSize savedSize)
    (beginIncrement + componentIncrement + stateIncrement + responseCap + 2)
    (extent_step componentExtent stateSize savedSize componentStep begin ready native code oracle
      beginIncrement componentIncrement stateIncrement responseCap hBegin hStep hReady hOracle)
    horizon elapsed hElapsed start target hTarget
  have hc := cells_bound componentCells componentExtent stateSize savedSize coefficient constant hComponent target
  have hq := Nat.pow_le_pow_left he 2
  have hl := Nat.mul_le_mul_left (coefficient + 10) he
  dsimp only [bound]
  omega

theorem bound_polynomial {initialExtent horizon beginIncrement componentIncrement stateIncrement responseCap : Nat → Nat}
    (hExtent : PolynomiallyBounded initialExtent) (hTime : PolynomiallyBounded horizon)
    (hBegin : PolynomiallyBounded beginIncrement) (hComponent : PolynomiallyBounded componentIncrement)
    (hState : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap) (coefficient constant : Nat) :
    PolynomiallyBounded (fun n => bound (initialExtent n) (horizon n) (beginIncrement n) (componentIncrement n)
      (stateIncrement n) (responseCap n) coefficient constant) := by
  have he := hExtent.add (hTime.mul ((((hBegin.add hComponent).add hState).add hResponse).add (PolynomiallyBounded.const 2)))
  have hb := ((((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const (coefficient + 10)).mul he)).add (PolynomiallyBounded.const constant)).add (PolynomiallyBounded.const 1)
  simpa only [bound, pow_two] using hb

end CryptoOracle.Interactive.ReusableResponseStorage
