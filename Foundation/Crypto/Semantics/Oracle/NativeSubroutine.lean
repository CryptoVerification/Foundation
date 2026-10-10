import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Machine.ClosedSubroutineArrival

/-! Invoke an existing closed native component as a prefix of interactive
code. The existing native subroutine compiler replaces halt with a real
return jump. All subsequent interactive instructions remain available. -/
namespace CryptoOracle.Interactive.NativeCode
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def subroutinePrefix (program : Machine.Program) : Code :=
  code (program.asSubroutine 0 (program.length + 1))

def returnBoundary {State : Type*} (address : Nat) (c : Configuration State) : Bool :=
  match c.control with
  | .running machine => machine.pc == address
  | _ => false

/-- The native first-halt joint law becomes the actual first-return joint
law in the interactive host, with exactly the same number of transitions. -/
theorem subroutine_first_joint {Input Output State : Type*}
    (P : NativeComponent Input Output) (tail : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (input : Input) :
    runToBoundary (Reification.timedStep (subroutinePrefix P.procedure.code ++ tail) oracle)
      (returnBoundary (P.procedure.code.length + 1)) (P.procedure.execution.budget input)
      (frame state trace (P.procedure.execution.entry input)) =
    (P.firstArrival.procedure.execution.costed input).map
      (fun result => (frame state trace (Machine.Program.subroutineState 0 (P.procedure.code.length + 1) result.1), result.2)) := by
  rw [P.firstArrival_costed]
  have transport := runToBoundary_map_on_invariant (Machine.stepPMF P.procedure.code)
    (Reification.timedStep (subroutinePrefix P.procedure.code ++ tail) oracle)
    Machine.Configuration.halted (returnBoundary (P.procedure.code.length + 1))
    (fun machine => frame state trace (Machine.Program.subroutineState 0 (P.procedure.code.length + 1) machine))
    (fun machine => machine.halted = true ∨ machine.pc < P.procedure.code.length)
    (by
      intro machine valid active next support
      have inside : machine.pc < P.procedure.code.length := valid.resolve_left (by simp [active])
      rcases (Machine.mem_support_stepPMF_iff _ _ _).mp support with actual | padded
      · cases hh : next.halted with
        | true => exact Or.inl rfl
        | false => exact Or.inr (P.closed machine next inside actual hh)
      · simp [active] at padded)
    (by
      intro machine valid
      cases hh : machine.halted with
      | true => simp [frame, returnBoundary, Machine.Program.subroutineState, hh, Machine.Configuration.resumeAt]
      | false =>
          have inside := valid.resolve_left (by simp [hh])
          simp [frame, returnBoundary, Machine.Program.subroutineState, hh, Machine.Configuration.rebasePc]
          omega)
    (by
      intro machine valid active
      have inside := valid.resolve_left (by simp [active])
      simp only [Machine.Program.subroutineState, active, Bool.false_eq_true, ↓reduceIte]
      have native := running_step_of_lookup
        (Machine.Program.withSubroutine [] P.procedure.code [] (P.procedure.code.length + 1))
        (subroutinePrefix P.procedure.code ++ tail) oracle state trace (machine.rebasePc 0)
        (by simp [Machine.Program.withSubroutine, Machine.Configuration.rebasePc]; omega)
        (by simpa [Machine.Configuration.rebasePc] using active)
        (by
          simp only [subroutinePrefix, code, Machine.Program.withSubroutine, List.nil_append, List.append_nil,
            Machine.Configuration.rebasePc, Nat.zero_add]
          rw [List.getElem?_append_left (by simp [Machine.Program.asSubroutine_length]; omega)]
          rw [List.getElem?_map]
          rfl)
      have invoked := Machine.Program.stepPMF_subroutineState [] P.procedure.code []
        (P.procedure.code.length + 1) (by intro pc hp; simp; omega) P.closed machine inside active
      simp only [List.length_nil] at invoked
      rw [native, invoked, PMF.map_comp]
      rfl)
    (P.procedure.execution.budget input) (P.procedure.execution.entry input) (Or.inr (P.entry input))
  have entry : Machine.Program.subroutineState 0 (P.procedure.code.length + 1)
      (P.procedure.execution.entry input) = P.procedure.execution.entry input := by
    simp only [Machine.Program.subroutineState, P.active input, Bool.false_eq_true, ↓reduceIte]
    cases P.procedure.execution.entry input; simp [Machine.Configuration.rebasePc]
  rw [entry] at transport
  exact transport

theorem subroutinePrefix_length (program : Machine.Program) :
    (subroutinePrefix program).length = program.length + 1 := by
  simp [subroutinePrefix, code]

end CryptoOracle.Interactive.NativeCode
