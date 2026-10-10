import Foundation.Crypto.Semantics.Oracle.OneUseSource
import Foundation.Crypto.Semantics.Procedure

/-! Real native tape operations embedded in an arbitrary interactive host.
The contract preserves private keys, opaque state and history. Its duration
is the number of original one-cell instructions, without a synthetic halt. -/
namespace CryptoOracle.Interactive.StraightLine
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

inductive Action where
  | left (which : Machine.TapeId)
  | right (which : Machine.TapeId)
  | write (which : Machine.TapeId) (cell : Option Bool)
  deriving DecidableEq, Repr

def instruction : Action → Machine.Instruction
  | .left which => .moveLeft which
  | .right which => .moveRight which
  | .write which none => .erase which
  | .write which (some bit) => .write which bit

def apply (action : Action) (machine : Machine.Configuration) : Machine.Configuration :=
  match action with
  | .left which => (machine.updateTape which Machine.Tape.moveLeft).advance
  | .right which => (machine.updateTape which Machine.Tape.moveRight).advance
  | .write which cell => (machine.updateTape which (fun tape => tape.write cell)).advance

def execute : List Action → Machine.Configuration → Machine.Configuration
  | [], machine => machine
  | action :: actions, machine => execute actions (apply action machine)

def code (actions : List Action) : Code := actions.map (fun action => .native (instruction action))

theorem execute_append (first second : List Action) (machine : Machine.Configuration) :
    execute (first ++ second) machine = execute second (execute first machine) := by
  induction first generalizing machine with
  | nil => rfl
  | cons action actions ih => exact ih (apply action machine)

theorem apply_pc (action : Action) (machine : Machine.Configuration) :
    (apply action machine).pc = machine.pc + 1 := by
  cases action with
  | left which => cases which <;> rfl
  | right which => cases which <;> rfl
  | write which _ => cases which <;> rfl

theorem apply_halted (action : Action) (machine : Machine.Configuration) :
    (apply action machine).halted = machine.halted := by
  cases action with
  | left which => cases which <;> rfl
  | right which => cases which <;> rfl
  | write which _ => cases which <;> rfl

theorem instruction_next (action : Action) (machine : Machine.Configuration) :
    (instruction action).next machine = .inl (apply action machine) := by
  cases action with
  | left which => rfl
  | right which => rfl
  | write which cell => cases cell <;> rfl

/-- Execute one tape action in the public controller, with no private callback
wrapper. This is the same native instruction and transition as `one` below. -/
theorem public_one {State : Type u} (host : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (action : Action) (machine : Machine.Configuration)
    (hActive : machine.halted = false)
    (hInstruction : host[machine.pc]? = some (.native (instruction action))) :
    Reification.timedStep host oracle ⟨state, .running machine, trace⟩ =
      PMF.pure ⟨state, .running (apply action machine), trace⟩ := by
  simp [Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, hActive, hInstruction, instruction_next]

/-- The existing straight-line code also runs directly in a public oracle
machine. No source halt, free tape reset, or host computation is inserted. -/
theorem public_run {State : Type u} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (before after : Code) (actions : List Action) (machine : Machine.Configuration)
    (hPc : machine.pc = before.length) (hActive : machine.halted = false) :
    TimedExecution.eval (Reification.timedStep (before ++ code actions ++ after) oracle) actions.length
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (execute actions machine), trace⟩ := by
  induction actions generalizing before machine with
  | nil => rfl
  | cons action actions ih =>
      rw [List.length_cons, TimedExecution.eval]
      rw [public_one _ oracle state trace action machine hActive (by simp [hPc, code])]
      rw [PMF.pure_bind]
      have h := ih (before ++ [.native (instruction action)]) (apply action machine)
        (by simp [apply_pc, hPc]) (by rw [apply_halted]; exact hActive)
      simpa only [code, List.map_cons, List.append_assoc, List.cons_append, List.nil_append, execute] using h

/-- Rewind previously traversed output cells while preserving arbitrary
left prefixes, blank cells and the complete right tail. Each cell costs one
ordinary native movement. Extracted from the existing packet writer. -/
def rewindOutputTape (before cells : List (Option Bool)) (cell : Option Bool)
    (after : List (Option Bool)) : Machine.Tape :=
  { left := before, current := (cells ++ cell :: after).headD none,
    right := (cells ++ cell :: after).tail }

theorem rewind_output (cells before after : List (Option Bool)) (cell : Option Bool)
    (machine : Machine.Configuration) :
    execute (List.replicate cells.length (.left .output))
      { machine with outputTape := { left := cells.reverse ++ before, current := cell, right := after } } =
      { machine with pc := machine.pc + cells.length, outputTape := rewindOutputTape before cells cell after } := by
  induction cells generalizing before machine with
  | nil => simp [execute, rewindOutputTape]
  | cons first cells ih =>
      rw [List.length_cons]
      -- Reversing the list puts its last cell at the head. Execute the
      -- shorter rewind first, then the remaining single left movement.
      have hr : List.replicate (cells.length + 1) (Action.left .output) =
          List.replicate cells.length (Action.left .output) ++ [Action.left .output] := by simp [List.replicate_add]
      rw [hr, execute_append]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [ih (first :: before)]
      cases cells <;> simp [execute, apply, rewindOutputTape, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Machine.Tape.moveLeft, Nat.add_assoc]

variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))

theorem one (host : Code) (action : Action) (machine : Machine.Configuration)
    (hActive : machine.halted = false)
    (hInstruction : host[machine.pc]? = some (.native (instruction action))) :
    OneUseSource.step native host oracle (.source false key ⟨state, .running machine, trace⟩) =
      PMF.pure (.source false key ⟨state, .running (apply action machine), trace⟩) := by
  simp [OneUseSource.step, Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, hActive, hInstruction, instruction_next, PMF.pure_map]

theorem run (before after : Code) (actions : List Action) (machine : Machine.Configuration)
    (hPc : machine.pc = before.length) (hActive : machine.halted = false) :
    TimedExecution.eval (OneUseSource.step native (before ++ code actions ++ after) oracle) actions.length
      (.source false key ⟨state, .running machine, trace⟩) =
      PMF.pure (.source false key ⟨state, .running (execute actions machine), trace⟩) := by
  induction actions generalizing before machine with
  | nil => rfl
  | cons action actions ih =>
      rw [List.length_cons, TimedExecution.eval]
      rw [one native oracle key state trace _ action machine hActive (by simp [hPc, code])]
      rw [PMF.pure_bind]
      have h := ih (before ++ [.native (instruction action)]) (apply action machine)
        (by simp [apply_pc, hPc]) (by rw [apply_halted]; exact hActive)
      simpa only [code, List.map_cons, List.append_assoc, List.cons_append, List.nil_append, execute] using h

noncomputable def procedure (before after : Code) (actions : List Action) (machine : Machine.Configuration)
    (hPc : machine.pc = before.length) (hActive : machine.halted = false) :
    Procedure (OneUseSource.step native (before ++ code actions ++ after) oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .source false key ⟨state, .running machine, trace⟩)
    (fun _ _ => .source false key ⟨state, .running (execute actions machine), trace⟩)
    (fun _ => PMF.pure ()) (fun _ => actions.length)
    (fun _ => by simpa only [PMF.pure_map] using run native oracle key state trace before after actions machine hPc hActive)

end CryptoOracle.Interactive.StraightLine
