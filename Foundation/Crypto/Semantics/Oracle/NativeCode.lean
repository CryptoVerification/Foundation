import Foundation.Crypto.Semantics.Oracle.ReificationExecution
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.BoundaryInvariantSimulation

/-! Embed existing native finite code in the interactive instruction list.
For a closed native component the actual first-halt joint law is preserved,
including arbitrary private oracle state and transcript prefixes. Falling
off malformed code is excluded by the existing control certificate. -/
namespace CryptoOracle.Interactive.NativeCode
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

def code (program : Machine.Program) : Code := program.map Instruction.native

def frame {State : Type u} (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration) : Configuration State := ⟨state, .running machine, trace⟩

/-- Native instructions can execute inside a mixed interactive instruction
list; only the currently fetched instruction must agree. -/
theorem running_step_of_lookup {State : Type*} (program : Machine.Program) (target : Code)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration) (inside : machine.pc < program.length)
    (active : machine.halted = false)
    (same : target[machine.pc]? = (program[machine.pc]?).map Instruction.native) :
    Reification.timedStep target oracle (frame state trace machine) =
      (Machine.stepPMF program machine).map (frame state trace) := by
  cases lookup : program[machine.pc]? with
  | none => simp at lookup; omega
  | some instruction =>
      have embedded : target[machine.pc]? = some (.native instruction) := by simpa [lookup] using same
      cases successor : instruction.next machine with
      | inl next =>
          simp [Reification.timedStep, Reification.terminal, frame, Reification.perform,
            Reification.action, transition, active, embedded, Machine.stepPMF, Machine.next,
            lookup, successor, PMF.pure_map]
      | inr pair =>
          simp [Reification.timedStep, Reification.terminal, frame, Reification.perform,
            Reification.action, transition, active, embedded, Machine.stepPMF, Machine.next,
            lookup, successor, PMF.map_comp, Function.comp_def]
          congr 1
          funext bit
          cases bit <;> rfl

theorem running_step {State : Type u} (program : Machine.Program) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (inside : machine.pc < program.length) (active : machine.halted = false) :
    Reification.timedStep (code program) oracle (frame state trace machine) =
      (Machine.stepPMF program machine).map (frame state trace) := by
  exact running_step_of_lookup program (code program) oracle state trace machine inside active
    (by simp [code, List.getElem?_map])

/-- A closed native program keeps its entire physical run when embedded in
the interactive machine. Private state and prior history are never read or
changed by the embedded instructions, including local random-bit steps. -/
theorem closed_eval {State : Type u} (program : Machine.Program) (oracle : BitOracle State)
    (closed : ∀ start target, start.pc < program.length → Machine.Step program start target →
      target.halted = false → target.pc < program.length)
    (state : State) (trace : List (List Bool × List Bool)) (fuel : Nat)
    (machine : Machine.Configuration)
    (valid : machine.halted = true ∨ machine.pc < program.length) :
    TimedExecution.eval (Reification.timedStep (code program) oracle) fuel (frame state trace machine) =
      (Machine.evalConfigWithin program machine fuel).map (frame state trace) := by
  induction fuel generalizing machine with
  | zero => simp [TimedExecution.eval, Machine.evalConfigWithin, PMF.pure_map]
  | succ fuel ih =>
      have unfoldNative : Machine.evalConfigWithin program machine (fuel + 1) =
          (Machine.stepPMF program machine).bind (fun next => Machine.evalConfigWithin program next fuel) := by
        rw [show fuel + 1 = 1 + fuel by omega, Machine.evalConfigWithin_add]
        simp [Machine.evalConfigWithin]
      rw [TimedExecution.eval, unfoldNative]
      cases active : machine.halted with
      | true =>
          simp only [Reification.timedStep, Reification.terminal, frame, active, ↓reduceIte,
            Machine.stepPMF, Machine.next, PMF.pure_bind]
          exact ih machine (Or.inl active)
      | false =>
          have inside : machine.pc < program.length := by simpa [active] using valid
          rw [running_step program oracle state trace machine inside active, PMF.bind_map, PMF.map_bind]
          rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
          congr 1
          funext next support
          apply ih
          cases halted : next.halted with
          | true => exact Or.inl rfl
          | false =>
              right
              apply closed machine next inside _ halted
              rcases (Machine.mem_support_stepPMF_iff _ _ _).mp support with actual | padded
              · exact actual
              · simp [active] at padded

/-- The same code and every represented cell are retained. Only the
interactive wrapper around the native state is added. -/
theorem first_joint {Input : Type v} {Output : Type w} {State : Type u}
    (P : NativeComponent Input Output) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (input : Input) :
    runToBoundary (Reification.timedStep (code P.procedure.code) oracle)
      (fun finish => Reification.terminal finish.control) (P.procedure.execution.budget input)
      (frame state trace (P.procedure.execution.entry input)) =
    (P.firstArrival.procedure.execution.costed input).map
      (fun result => (frame state trace result.1, result.2)) := by
  rw [P.firstArrival_costed]
  apply runToBoundary_map_on_invariant (Machine.stepPMF P.procedure.code) _
    Machine.Configuration.halted _ (frame state trace)
    (fun machine => machine.halted = true ∨ machine.pc < P.procedure.code.length)
  · intro machine valid active next support
    have inside : machine.pc < P.procedure.code.length := by
      rcases valid with h | h
      · simp [active] at h
      · exact h
    rcases (Machine.mem_support_stepPMF_iff _ _ _).mp support with actual | padded
    · cases hn : next.halted with
      | true => exact Or.inl rfl
      | false => exact Or.inr (P.closed machine next inside actual hn)
    · simp [active] at padded
  · intro machine _; rfl
  · intro machine valid active
    apply running_step
    · rcases valid with h | h
      · simp [active] at h
      · exact h
    · exact active
  · exact Or.inr (P.entry input)

end CryptoOracle.Interactive.NativeCode
