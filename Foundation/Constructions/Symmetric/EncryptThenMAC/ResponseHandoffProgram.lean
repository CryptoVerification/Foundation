import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoff
import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Arbitrary finite response-processing program and arbitrary payload size.
Payload writing, retained-key copying, rewind and ownership transfer are
charged physical transitions. Handler semantics remain a proved contract. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def step (program : Program) : ResponseHandoff.Control → PMF ResponseHandoff.Control
  | .authenticating key machine => (stepPMF program machine).map (.authenticating key)
  | other => ResponseHandoff.step other

noncomputable def eval (program : Program) := TimedExecution.eval (step program)

theorem original_step (c : ResponseHandoff.Control) : step AuthenticateResponse.code c = ResponseHandoff.step c := by
  cases c <;> rfl

theorem header_eval (program : Program) (key : Tape) (remaining : List Bool) (before : List (Option Bool)) :
    eval program (2 * remaining.length + 1) (.headerWriting key remaining { left := before }) =
      PMF.pure (.copying { inputTape := key, outputTape := { left := remaining.reverse.map some ++ before } }) := by
  induction remaining generalizing before with
  | nil => simp [eval, TimedExecution.eval, step, ResponseHandoff.step, PMF.pure_bind]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega]
      simp only [eval, TimedExecution.eval, step, ResponseHandoff.step, Tape.write, PMF.pure_bind]
      change eval program (2 * remaining.length + 1)
        (.headerWriting key remaining { left := some bit :: before }) = _
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_eval (program : Program) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (key : Tape) :
    eval program (left.length + 1) (.rewinding key ⟨left.map some, current, right⟩) =
      PMF.pure (.authenticating key { inputTape := ResponseHandoff.fromCells (left.reverse.map some ++ current :: right) }) := by
  induction left generalizing current right with
  | nil => simp [eval, TimedExecution.eval, step, ResponseHandoff.step, ResponseHandoff.fromCells, PMF.pure_bind]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl]
      simp only [eval, TimedExecution.eval, step, ResponseHandoff.step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      change eval program (left.length + 1) (.rewinding key ⟨left.map some, some bit, current :: right⟩) = _
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def retainedKey (key : List Bool) := PrivateKeyCopy.restored (key.map some ++ [none])
def preparedMachine (key payload : List Bool) : Machine.Configuration :=
  { inputTape := ResponseHandoff.fromCells ((payload ++ key).map some ++ [none]) }

theorem copied_to_handler (program : Program) (key payload : List Bool) :
    eval program (key.length + payload.length + 2)
      (.copying (PrivateKeyCopy.finish key (payload.reverse.map some))) =
      PMF.pure (.authenticating (retainedKey key) (preparedMachine key payload)) := by
  rw [show key.length + payload.length + 2 = (key.length + payload.length + 1) + 1 by omega]
  simp only [eval, TimedExecution.eval, step, ResponseHandoff.step, PrivateKeyCopy.finish,
    ↓reduceIte, PMF.pure_bind]
  change eval program (key.length + payload.length + 1)
    (.rewinding (retainedKey key) { left := key.reverse.map some ++ payload.reverse.map some }) = _
  have h := rewind_eval program (key.reverse ++ payload.reverse) none [] (retainedKey key)
  simpa [List.length_append, List.length_reverse, List.map_append, List.reverse_append,
    List.reverse_reverse, preparedMachine] using h

noncomputable def writePayload (program : Program) (key payload : List Bool) :=
  TimedExecution.Procedure.ofFixed (step program)
    (fun _ : Unit => ResponseHandoff.Control.headerWriting (Tape.ofBits key) payload {})
    (fun _ _ : Unit => ResponseHandoff.Control.copying (PrivateKeyCopy.copying [] key (payload.reverse.map some)))
    (fun _ => PMF.pure ()) (fun _ => 2 * payload.length + 1) (by
      intro input
      have h := header_eval program (Tape.ofBits key) payload []
      cases key
      simpa only [eval, PMF.pure_map, PrivateKeyCopy.copying, Tape.ofBits, List.reverse_nil, List.map_nil, List.append_nil] using
        h
      simpa only [eval, PMF.pure_map, PrivateKeyCopy.copying, Tape.ofBits, List.reverse_nil, List.map_nil, List.append_nil] using
        h)

private noncomputable def copyNative (key payload : List Bool) :=
  Machine.Procedure.ofFixed PrivateKeyCopy.code
    (fun _ : Unit => PrivateKeyCopy.copying [] key (payload.reverse.map some))
    (fun _ _ : Unit => PrivateKeyCopy.finish key (payload.reverse.map some))
    (fun _ => PMF.pure ()) (fun _ => 8 * key.length + 5)
    (fun _ => by simpa only [PMF.pure_map] using PrivateKeyCopy.run key (payload.reverse.map some))

private def copyBoundary : ResponseHandoff.Control → Bool
  | .copying machine => machine.halted | _ => false

noncomputable def copyKey (program : Program) (key payload : List Bool) :=
  (copyNative key payload).execution.liftBoundary (fun c => c.halted)
    (by intro input output h; rfl)
    (by intro c hc; simp [stepPMF, next, hc])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step program) copyBoundary ResponseHandoff.Control.copying (fun _ => rfl)
    (by intro c hc; simp [step, ResponseHandoff.step, hc, copyNative, Machine.Procedure.ofFixed])

noncomputable def transfer (program : Program) (key payload : List Bool) :=
  TimedExecution.Procedure.ofFixed (step program)
    (fun _ : Unit => ResponseHandoff.Control.copying (PrivateKeyCopy.finish key (payload.reverse.map some)))
    (fun _ _ : Unit => ResponseHandoff.Control.authenticating (retainedKey key) (preparedMachine key payload))
    (fun _ => PMF.pure ()) (fun _ => key.length + payload.length + 2)
    (fun _ => by simpa only [eval, PMF.pure_map] using copied_to_handler program key payload)

noncomputable def preparation (program : Program) (key payload : List Bool) :=
  ((writePayload program key payload).seq (copyKey program key payload)
    (fun _ _ _ => rfl) (fun _ => 8 * key.length + 5) (fun _ _ _ => Nat.le_refl _)).seq
    ((transfer program key payload).reindex (fun _ : Unit × Unit => ()))
    (fun _ _ _ => rfl) (fun _ => key.length + payload.length + 2) (fun _ _ _ => Nat.le_refl _)

/-- The preparatory interval is independent of the response-processing code.
The actual cost distribution records the retained-copy stopping time. -/
theorem preparation_budget (program : Program) (key payload : List Bool) :
    (preparation program key payload).budget () = 9 * key.length + 3 * payload.length + 8 := by
  change (2 * payload.length + 1) + (8 * key.length + 5) + (key.length + payload.length + 2) = _
  omega

theorem preparation_semantics (program : Program) (key payload : List Bool) :
    (preparation program key payload).semantics () = PMF.pure (((), ()), ()) := by
  change ((PMF.pure ()).bind (fun _ => (PMF.pure ()).map (fun output => ((), output)))).bind
    (fun middle => (PMF.pure ()).map (fun output => (middle, output))) = _
  simp only [PMF.pure_bind, PMF.pure_map]

theorem retained_key (key : List Bool) : (retainedKey key).Equivalent (Tape.ofBits key) :=
  PrivateKeyCopy.key_restored key []

noncomputable def complete {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload) :=
  (preparation program key payload).seq
    ((handler.transport (step program) (.authenticating (retainedKey key)) (fun _ => rfl)).reindex
      (fun _ : (Unit × Unit) × Unit => ()))
    (by intro _ _ _; change ResponseHandoff.Control.authenticating _ (handler.entry ()) = _; rw [hEntry]; rfl)
    (fun _ => handler.budget ()) (fun _ _ _ => Nat.le_refl _)

theorem complete_budget {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload) :
    (complete program key payload handler hEntry).budget () =
      9 * key.length + 3 * payload.length + 8 + handler.budget () := by
  change (preparation program key payload).budget () + handler.budget () = _
  rw [preparation_budget]

theorem complete_entry {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload) :
    (complete program key payload handler hEntry).entry () =
      .headerWriting (Tape.ofBits key) payload {} := rfl

theorem complete_exit {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload) (output : Output) :
    (complete program key payload handler hEntry).exit () ((((), ()), ()), output) =
      .authenticating (retainedKey key) (handler.exit () output) := rfl

theorem complete_semantics {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload) :
    (complete program key payload handler hEntry).semantics () =
      (handler.semantics ()).map (fun output => ((((), ()), ()), output)) := by
  change ((preparation program key payload).semantics ()).bind
    (fun middle => (handler.semantics ()).map (fun output => (middle, output))) = _
  rw [preparation_semantics, PMF.pure_bind]

theorem budget_polynomial {keyLength payloadLength handlerBudget : Nat → Nat}
    (hKey : PolynomiallyBounded keyLength) (hPayload : PolynomiallyBounded payloadLength)
    (hHandler : PolynomiallyBounded handlerBudget) :
    PolynomiallyBounded (fun n => 9 * keyLength n + 3 * payloadLength n + 8 + handlerBudget n) :=
  (((((PolynomiallyBounded.const 9).mul hKey).add ((PolynomiallyBounded.const 3).mul hPayload)).add
    (PolynomiallyBounded.const 8)).add hHandler)

/-- At any sufficiently large horizon, a certified halted handler produces
its exact full native state while the retained private key remains separate. -/
theorem complete_run {Output : Type u} (program : Program) (key payload : List Bool)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (hEntry : handler.entry () = preparedMachine key payload)
    (hHalt : ∀ output ∈ (handler.semantics ()).support, (handler.exit () output).halted = true)
    (horizon : Nat) (hBudget : 9 * key.length + 3 * payload.length + 8 + handler.budget () ≤ horizon) :
    eval program horizon (.headerWriting (Tape.ofBits key) payload {}) =
      (handler.semantics ()).map (fun output => .authenticating (retainedKey key) (handler.exit () output)) := by
  have hp := (complete program key payload handler hEntry).final_run () (by
    intro result hResult
    rw [complete_semantics, PMF.mem_support_map_iff] at hResult
    obtain ⟨output, hOutput, rfl⟩ := hResult
    rw [complete_exit]
    simp [step, stepPMF, next, hHalt output hOutput, PMF.pure_map]) horizon
    (by rw [complete_budget]; exact hBudget)
  simpa only [eval, complete_entry, complete_semantics, PMF.map_comp, Function.comp_def, complete_exit] using hp

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
