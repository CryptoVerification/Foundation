import Foundation.Crypto.Semantics.Oracle.ResponseLoading

/-! Exact execution of the existing cell-by-cell oracle-call controller.
The caller's input tape and finite control are retained. Only the explicitly
loaded response replaces its output tape. Oracle evaluation costs one capability
transition; this theorem does not charge computation inside that capability. -/
namespace CryptoOracle.Interactive.CallExecution
open Foundation.Probability Machine TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (code : Code) (oracle : BitOracle State)

theorem sending_run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining accumulated : List Bool)
    (left : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (remaining.length + 1)
      (⟨state, .sending machine { ResponseLoading.loaded remaining with left := left }
        accumulated, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .reversing machine (remaining.reverse ++ accumulated) [], trace⟩ := by
  induction remaining generalizing accumulated left with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition,
        ResponseLoading.loaded, ResponseLoading.fromCells]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl,
        TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, Reification.perform, Reification.action, transition,
        ResponseLoading.loaded, List.map_cons, List.cons_append,
        ResponseLoading.fromCells, List.headD_cons, List.tail_cons, Tape.moveRight,
        PMF.pure_bind]
      have h := ih (bit :: accumulated) (some bit :: left)
      cases remaining <;> simpa [ResponseLoading.loaded, ResponseLoading.fromCells,
        List.reverse_cons, List.append_assoc] using h

theorem reversing_run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) (remaining.length + 1)
      (⟨state, .reversing machine remaining request, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩ := by
  induction remaining generalizing request with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl,
        TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, Reification.perform, Reification.action, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Starting at a real call instruction, transfer the whole request, invoke
the oracle once, and resume at the next instruction with its response loaded.
All supported responses must have the displayed fixed width; neither the
response value nor the updated private oracle state is otherwise restricted. -/
theorem run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (responseWidth : Nat)
    (running : machine.halted = false) (instruction : code[machine.pc]? = some .call)
    (packet : machine.outputTape = ResponseLoading.loaded request)
    (width : ∀ answer ∈ (oracle state request).support, answer.2.length = responseWidth) :
    TimedExecution.eval (Reification.timedStep code oracle)
      (2 * request.length + 3 * responseWidth + 6)
      (⟨state, .running machine, trace⟩ : Configuration State) =
    (oracle state request).map (fun answer =>
      (⟨answer.1, .running { machine.advance with outputTape := ResponseLoading.loaded answer.2 },
        (request, answer.2) :: trace⟩ : Configuration State)) := by
  have first : TimedExecution.eval (Reification.timedStep code oracle) 1
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .sending machine.advance (ResponseLoading.loaded request) [], trace⟩ := by
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, running, instruction, packet]
  rw [show 2 * request.length + 3 * responseWidth + 6 =
      1 + ((request.length + 1) + ((request.reverse.length + 1) + (1 + (3 * responseWidth + 2)))) by simp; omega,
    TimedExecution.eval_add, first, PMF.pure_bind, TimedExecution.eval_add]
  have sent := sending_run code oracle machine.advance state trace request [] []
  simp only [List.append_nil] at sent
  have empty_left : ({ ResponseLoading.loaded request with left := [] } : Tape) =
      ResponseLoading.loaded request := by rfl
  rw [empty_left] at sent
  rw [sent, PMF.pure_bind, TimedExecution.eval_add, reversing_run]
  simp only [List.reverse_reverse, List.append_nil, PMF.pure_bind]
  rw [TimedExecution.eval_add]
  simp only [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Bool.false_eq_true, ↓reduceIte, Reification.perform, Reification.action,
    transition, PMF.bind_pure, PMF.bind_map, Function.comp_def]
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = (oracle state request).bindOnSupport (fun answer _ => PMF.pure
        (⟨answer.1, .running { machine.advance with outputTape := ResponseLoading.loaded answer.2 },
          (request, answer.2) :: trace⟩ : Configuration State)) := by
      congr 1
      funext answer hAnswer
      rw [← width answer hAnswer]
      exact ResponseLoading.run code oracle machine.advance answer.1
        ((request, answer.2) :: trace) answer.2
    _ = _ := by rw [PMF.bindOnSupport_eq_bind]; rfl

end CryptoOracle.Interactive.CallExecution
