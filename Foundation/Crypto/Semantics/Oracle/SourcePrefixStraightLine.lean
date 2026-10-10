import Foundation.Crypto.Semantics.Oracle.SourcePrefix
import Foundation.Crypto.Semantics.Oracle.StraightLine

/-! Ordinary native tape operations before the next captured source request.
The source boundary does not shortcut any executed instruction. -/
namespace CryptoOracle.Interactive.SourcePrefix
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- Reuse the existing straight-line emitter under the actual first-request
boundary semantics. Only active native instructions are used in this prefix. -/
theorem straight_run {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (before after : Code) (actions : List StraightLine.Action) (machine : Machine.Configuration)
    (pc : machine.pc = before.length) (active : machine.halted = false) :
    TimedExecution.eval (step (before ++ StraightLine.code actions ++ after) oracle) actions.length
      (⟨state, .running machine, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running (StraightLine.execute actions machine), trace⟩ := by
  induction actions generalizing before machine with
  | nil => rfl
  | cons action actions ih =>
      rw [List.length_cons, TimedExecution.eval]
      have one : step (before ++ StraightLine.code (action :: actions) ++ after) oracle
          ⟨state, .running machine, trace⟩ =
          PMF.pure ⟨state, .running (StraightLine.apply action machine), trace⟩ := by
        rw [step, show boundary (⟨state, .running machine, trace⟩ : Configuration State) = false by
          simp [boundary, Reification.terminal, active]]
        exact StraightLine.public_one _ oracle state trace action machine active
          (by simp [pc, StraightLine.code])
      rw [one, PMF.pure_bind]
      have h := ih (before ++ [.native (StraightLine.instruction action)]) (StraightLine.apply action machine)
        (by simp [StraightLine.apply_pc, pc]) (by rw [StraightLine.apply_halted]; exact active)
      simpa only [StraightLine.code, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append, StraightLine.execute] using h
end CryptoOracle.Interactive.SourcePrefix
