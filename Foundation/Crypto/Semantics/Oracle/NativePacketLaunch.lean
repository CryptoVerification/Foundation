import Foundation.Crypto.Semantics.Oracle.NativePacketComponent
import Foundation.Crypto.Semantics.Machine.NativePacketPreparationExactTime
import Foundation.Crypto.Semantics.Machine.TapeSwap
import Foundation.Crypto.Semantics.BoundaryComposition

/-! Charge the existing raw loader before entering an interactive component.
The controller hands over the two actual tapes, either in their original
roles or with their operand roles reversed. It does not normalize cells.
The initial request buffer and blank loading tape are physical preconditions.
The ownership handoff is a controller transition, not a native tape-swap
instruction or a unit-cost request encoder. -/
namespace CryptoOracle.Interactive.NativePacketLaunch
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | preparing (state : State) (loader : Machine.NativePacketService.Control)
  | running (component : NativePacketComponent.Control State)

def handoffFrame {State : Type u} (state : State) (machine : Machine.Configuration)
    (reverseRoles : Bool := true) (prior : List (List Bool × List Bool) := []) : Configuration State :=
  ⟨state, .running (match reverseRoles with | true => machine.swapTapes | false => machine), prior⟩

noncomputable def step {State : Type u} (code : Code) (oracle : BitOracle State)
    (reverseRoles : Bool := true) (prior : List (List Bool × List Bool) := []) : Control State → PMF (Control State)
  | .preparing state (.executing (.running machine)) =>
      PMF.pure (.running (.computing (handoffFrame state machine reverseRoles prior)))
  | .preparing state loader =>
      (Machine.NativePacketService.step [] loader).map (.preparing state)
  | .running component => (NativePacketComponent.step code oracle component).map .running

def preparationBoundary {State : Type u} : Control State → Bool
  | .preparing _ loader => Machine.NativePacketService.preparedBoundary loader
  | .running _ => true

def runningBoundary {State : Type u} : Control State → Bool
  | .preparing _ _ => false
  | .running _ => true

/-- Once launched, every component transition, including physical packet
export, is executed by the unchanged outer controller. -/
theorem running_eval {State : Type u} (code : Code) (oracle : BitOracle State)
    (reverseRoles : Bool) (prior : List (List Bool × List Bool))
    (fuel : Nat) (component : NativePacketComponent.Control State) :
    TimedExecution.eval (step code oracle reverseRoles prior) fuel (.running component) =
      (TimedExecution.eval (NativePacketComponent.step code oracle) fuel component).map .running := by
  induction fuel generalizing component with
  | zero => simp [TimedExecution.eval, PMF.pure_map]
  | succ fuel ih =>
      simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]

variable {State : Type u} (code : Code) (oracle : BitOracle State) (state : State) (request : List Bool)

/-- The source loader's exact first-arrival law is reused without changing
any of its writing or rewinding transitions. -/
theorem preparation_first_joint (reverseRoles : Bool := true)
    (prior : List (List Bool × List Bool) := []) :
    runToBoundary (step code oracle reverseRoles prior) preparationBoundary (3 * request.length + 3)
      (.preparing state (.loading request {})) =
    PMF.pure (.preparing state (.executing (.running (Machine.NativePacketService.loaded request))),
      3 * request.length + 3) := by
  rw [runToBoundary_map (Machine.NativePacketService.step []) (step code oracle reverseRoles prior)
    Machine.NativePacketService.preparedBoundary preparationBoundary (.preparing state)
    (fun _ => rfl) (by
      intro loader notPrepared
      cases loader <;> simp_all [Machine.NativePacketService.preparedBoundary, step]),
    Machine.NativePacketService.preparation_first_joint, PMF.pure_map]

/-- The exact first component entry includes the ownership transfer. -/
theorem launch_first_joint (reverseRoles : Bool := true)
    (prior : List (List Bool × List Bool) := []) :
    runToBoundary (step code oracle reverseRoles prior) runningBoundary (3 * request.length + 4)
      (.preparing state (.loading request {})) =
    PMF.pure (.running (.computing (handoffFrame state (Machine.NativePacketService.loaded request) reverseRoles prior)),
      3 * request.length + 4) := by
  have hp := preparation_first_joint code oracle state request reverseRoles prior
  have hn : runToBoundary (step code oracle reverseRoles prior) runningBoundary 1
      (.preparing state (.executing (.running (Machine.NativePacketService.loaded request)))) =
      PMF.pure (.running (.computing (handoffFrame state (Machine.NativePacketService.loaded request) reverseRoles prior)), 1) := by
    simp [runToBoundary, runningBoundary, step, PMF.pure_map]
  rw [show 3 * request.length + 4 = (3 * request.length + 3) + 1 by omega,
    runToBoundary_compose (step code oracle reverseRoles prior) preparationBoundary runningBoundary (fun _ => True)
      (by intros; trivial)
      (by intro control _ h; cases control <;> simp_all [preparationBoundary, runningBoundary])
      (3 * request.length + 3) 1 (.preparing state (.loading request {})) trivial
      (by
        intro middle hm
        rw [hp, PMF.mem_support_pure_iff] at hm
        subst middle
        rfl)
      (by
        intro middle hm result hr
        rw [hp, PMF.mem_support_pure_iff] at hm
        subst middle
        rw [hn, PMF.mem_support_pure_iff] at hr
        subst result
        rfl), hp, PMF.pure_bind, hn, PMF.pure_map]

/-- A later horizon resumes the same component after its actual entry time. -/
theorem launch_continues (horizon : Nat) (enough : 3 * request.length + 4 ≤ horizon)
    (reverseRoles : Bool := true) (prior : List (List Bool × List Bool) := []) :
    TimedExecution.eval (step code oracle reverseRoles prior) horizon (.preparing state (.loading request {})) =
    TimedExecution.eval (step code oracle reverseRoles prior) (horizon - (3 * request.length + 4))
      (.running (.computing (handoffFrame state (Machine.NativePacketService.loaded request) reverseRoles prior))) := by
  rw [runToBoundary_law (step code oracle reverseRoles prior) runningBoundary (3 * request.length + 4)
    horizon (.preparing state (.loading request {})) enough, launch_first_joint code oracle state request reverseRoles prior, PMF.pure_bind]

end CryptoOracle.Interactive.NativePacketLaunch
