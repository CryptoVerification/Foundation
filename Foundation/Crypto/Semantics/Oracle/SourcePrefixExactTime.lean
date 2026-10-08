import Foundation.Crypto.Semantics.Oracle.SourcePrefix
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! First request capture time, retaining the actual source machine.
The local boundary is absorbing; the outer caller need not be. -/
namespace CryptoOracle.Interactive.SourcePrefix
open Foundation.Probability TimedExecution
universe u
variable {State : Type u} (code : Code) (oracle : BitOracle State)
set_option backward.isDefEq.respectTransparency false

theorem reverse_before_capture (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (step code oracle) remaining.length
      (⟨state, .reversing machine remaining request, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .reversing machine [] (remaining.reverse ++ request), trace⟩ := by
  induction remaining generalizing request with
  | nil => simp [TimedExecution.eval]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length = remaining.length + 1 by rfl, TimedExecution.eval]
      simp only [step, boundary, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.timedStep, Reification.perform, Reification.action, transition, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem capture_before (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (step code oracle) (2 * request.length + 2)
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .reversing machine.advance [] request, trace⟩ := by
  rw [show 2 * request.length + 2 = (2 * request.length + 1) + 1 by omega, TimedExecution.eval]
  simp only [step, boundary, Reification.timedStep, Reification.terminal, hActive,
    Bool.false_eq_true, ↓reduceIte, Reification.perform, Reification.action, transition, hCall, PMF.pure_bind]
  rw [hTape, show 2 * request.length + 1 = (request.length + 1) + request.reverse.length by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse_before_capture]
  simp

theorem capture_first_joint (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    runToBoundary (step code oracle) boundary (2 * request.length + 3)
      ⟨state, .running machine, trace⟩ =
    PMF.pure (⟨state, .awaiting machine.advance request, trace⟩, 2 * request.length + 3) := by
  have hb := capture_before code oracle machine state trace request before after hActive hCall hTape
  have ha := capture_run code oracle machine state trace request before after hActive hCall hTape
  have h := runToBoundary_joint_of_adjacent (step code oracle) boundary
    ⟨state, .running machine, trace⟩ (2 * request.length + 2)
    (fun frame hf => by simp [step, hf])
    (by
      intro frame hf
      rw [hb, PMF.mem_support_pure_iff] at hf
      subst frame; rfl)
    (by
      intro frame hf
      rw [show 2 * request.length + 2 + 1 = 2 * request.length + 3 by omega, ha,
        PMF.mem_support_pure_iff] at hf
      subst frame; rfl)
  simpa only [show 2 * request.length + 2 + 1 = 2 * request.length + 3 by omega,
    ha, PMF.pure_map] using h

end CryptoOracle.Interactive.SourcePrefix
