import Foundation.Crypto.Semantics.Oracle.ReusableResponseInitialization
import Foundation.Crypto.Semantics.Oracle.ReusableResponseStorage

/-! Count initialization, alignment and all repeated-request states together.
The original caller remains counted even after activation, because it is a
parameter of the unchanged outer transition function. -/
namespace CryptoOracle.Interactive.ReusableInitializationStorage
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v}
    (componentCells componentExtent : Component → Nat) (stateSize : State → Nat)
    (caller : Configuration State)

def phaseCells : ReusableResponseInitialization.Control Component State → Nat
  | .initializing component => Machine.ControllerStorage.initializationCells component
  | .aligning tape => tape.cells
  | .active source => ReusableResponseStorage.cells componentCells stateSize Machine.Tape.cells source

def phaseExtent : ReusableResponseInitialization.Control Component State → Nat
  | .initializing component => Machine.ControllerExtent.initialization component
  | .aligning tape => tape.cells
  | .active source => ReusableResponseStorage.extent componentExtent stateSize Machine.Tape.cells source

def cells (c : ReusableResponseInitialization.Control Component State) :=
  SourceStorage.cells stateSize caller + phaseCells componentCells stateSize c

def extent (c : ReusableResponseInitialization.Control Component State) :=
  max (ControllerExtent.frameExtent stateSize caller) (phaseExtent componentExtent stateSize c)

variable (coefficient constant : Nat)
    (hComponent : ∀ c, componentCells c ≤ coefficient * componentExtent c + constant)

include hComponent in
theorem cells_bound (c : ReusableResponseInitialization.Control Component State) :
    cells componentCells stateSize caller c ≤ 6 * (extent componentExtent stateSize caller c) ^ 2 +
      (coefficient + 15) * extent componentExtent stateSize caller c + constant + 2 := by
  have hf := ControllerExtent.frame_cells stateSize caller
  have hfe : ControllerExtent.frameExtent stateSize caller ≤ extent componentExtent stateSize caller c := Nat.le_max_left _ _
  have hpe : phaseExtent componentExtent stateSize c ≤ extent componentExtent stateSize caller c := Nat.le_max_right _ _
  have hq := Nat.pow_le_pow_left hfe 2
  cases c with
  | initializing component =>
      have hp := Machine.ControllerExtent.initialization_cells component
      simp only [cells, phaseCells, phaseExtent] at *
      nlinarith
  | aligning tape =>
      simp only [cells, phaseCells, phaseExtent] at *
      nlinarith
  | active source =>
      have hp := ReusableResponseStorage.cells_bound componentCells componentExtent stateSize Machine.Tape.cells coefficient constant hComponent source
      have hqp := Nat.pow_le_pow_left hpe 2
      have hl := Nat.mul_le_mul_left (coefficient + 10) hpe
      simp only [cells, phaseCells, phaseExtent] at *
      nlinarith

variable (componentStep : Component → PMF Component)
    (begin : Machine.Tape → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Machine.Tape))
    (generator native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (increment : Nat)
    (hActive : ∀ start target, target ∈ (ReusableResponseSource.step componentStep begin ready native code oracle start).support →
      ReusableResponseStorage.extent componentExtent stateSize Machine.Tape.cells target ≤
        ReusableResponseStorage.extent componentExtent stateSize Machine.Tape.cells start + increment)

include hActive in
theorem extent_step (start target : ReusableResponseInitialization.Control Component State)
    (h : target ∈ (ReusableResponseInitialization.step componentStep begin ready generator native code oracle caller start).support) :
    extent componentExtent stateSize caller target ≤ extent componentExtent stateSize caller start + (increment + 1) := by
  cases start with
  | initializing component =>
      cases component with
      | ready key =>
          simp only [ReusableResponseInitialization.step, PMF.mem_support_pure_iff] at h
          subst target
          have hb := Machine.Tape.cells_moveLeft_le key
          simp only [extent, phaseExtent, Machine.ControllerExtent.initialization]
          omega
      | _ =>
          simp only [ReusableResponseInitialization.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := Machine.ControllerExtent.initialization_bound generator _ next hn
          simp only [extent, phaseExtent]
          omega
  | aligning key =>
      simp only [ReusableResponseInitialization.step, PMF.mem_support_pure_iff] at h
      subst target
      have hb := Machine.Tape.cells_moveRight_le key
      simp only [extent, phaseExtent, ReusableResponseStorage.extent]
      omega
  | active source =>
      simp only [ReusableResponseInitialization.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hb := hActive source next hn
      simp only [extent, phaseExtent]
      omega

def bound (initialExtent horizon increment coefficient constant : Nat) :=
  let e := initialExtent + horizon * (increment + 1)
  6 * e ^ 2 + (coefficient + 15) * e + constant + 2

include hComponent hActive in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : ReusableResponseInitialization.Control Component State)
    (hTarget : target ∈ (TimedExecution.eval
      (ReusableResponseInitialization.step componentStep begin ready generator native code oracle caller) elapsed start).support) :
    cells componentCells stateSize caller target ≤ bound (extent componentExtent stateSize caller start) horizon increment coefficient constant := by
  have he := ResourceGrowth.prefix_bound (ReusableResponseInitialization.step componentStep begin ready generator native code oracle caller)
    (extent componentExtent stateSize caller) (increment + 1)
    (extent_step componentExtent stateSize caller componentStep begin ready generator native code oracle increment hActive)
    horizon elapsed hElapsed start target hTarget
  have hc := cells_bound componentCells componentExtent stateSize caller coefficient constant hComponent target
  have hq := Nat.pow_le_pow_left he 2
  have hl := Nat.mul_le_mul_left (coefficient + 15) he
  dsimp only [bound]
  omega

theorem bound_polynomial {initialExtent horizon increment : Nat → Nat}
    (hInitial : PolynomiallyBounded initialExtent) (hTime : PolynomiallyBounded horizon)
    (hIncrement : PolynomiallyBounded increment) (coefficient constant : Nat) :
    PolynomiallyBounded (fun n => bound (initialExtent n) (horizon n) (increment n) coefficient constant) := by
  have he := hInitial.add (hTime.mul (hIncrement.add (PolynomiallyBounded.const 1)))
  have hb := ((((PolynomiallyBounded.const 6).mul (he.mul he)).add
    ((PolynomiallyBounded.const (coefficient + 15)).mul he)).add (PolynomiallyBounded.const constant)).add (PolynomiallyBounded.const 2)
  simpa only [bound, pow_two] using hb

end CryptoOracle.Interactive.ReusableInitializationStorage
