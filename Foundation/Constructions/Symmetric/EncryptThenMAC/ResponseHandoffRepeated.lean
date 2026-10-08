import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffProgramResources
import Foundation.Crypto.Semantics.Machine.RetainedCopyRepeated

/-! Response preparation and certified continuation from the exact retained
key layout produced by a preceding invocation. No tape normalization occurs. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Repeated
open Machine Foundation.Probability TimedExecution
open Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
open PrivacyEncoding (responderPc)
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def writePayload (program : Program) (key payload : List Bool) :=
  TimedExecution.Procedure.ofFixed (step program)
    (fun _ : Unit => ResponseHandoff.Control.headerWriting (retainedKey key) payload {})
    (fun _ _ : Unit => ResponseHandoff.Control.copying
      { inputTape := retainedKey key, outputTape := { left := payload.reverse.map some } })
    (fun _ => PMF.pure ()) (fun _ => 2 * payload.length + 1)
    (fun _ => by simpa only [eval, List.append_nil, PMF.pure_map] using
      header_eval program (retainedKey key) payload [])

private noncomputable def copyNative (key payload : List Bool) :=
  Machine.Procedure.ofFixed PrivateKeyCopy.code
    (fun _ : Unit => { inputTape := retainedKey key, outputTape := { left := payload.reverse.map some } })
    (fun _ _ : Unit => PrivateKeyCopy.finish key (payload.reverse.map some))
    (fun _ => PMF.pure ()) (fun _ => 8 * key.length + 5)
    (fun _ => by simpa only [PMF.pure_map, retainedKey, PrivateKeyCopy.restored, PrivateKeyCopy.code_eq_shared, PrivateKeyCopy.finish, Machine.RetainedCopy.finish, Machine.RetainedCopy.restored] using Machine.RetainedCopy.run_retained key (payload.reverse.map some))

private def copyBoundary : ResponseHandoff.Control → Bool
  | .copying machine => machine.halted | _ => false

noncomputable def copyKey (program : Program) (key payload : List Bool) :=
  (copyNative key payload).execution.liftBoundary (fun c => c.halted)
    (by intro input output h; rfl)
    (by intro c hc; simp [stepPMF, next, hc])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step program) copyBoundary ResponseHandoff.Control.copying (fun _ => rfl)
    (by intro c hc; simp [step, ResponseHandoff.step, hc, copyNative, Machine.Procedure.ofFixed])

noncomputable abbrev transfer := ResponseHandoffProgram.transfer

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
      .headerWriting (retainedKey key) payload {} := rfl

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
    eval program horizon (.headerWriting (retainedKey key) payload {}) =
      (handler.semantics ()).map (fun output => .authenticating (retainedKey key) (handler.exit () output)) := by
  have hp := (complete program key payload handler hEntry).final_run () (by
    intro result hResult
    rw [complete_semantics, PMF.mem_support_map_iff] at hResult
    obtain ⟨output, hOutput, rfl⟩ := hResult
    rw [complete_exit]
    simp [step, stepPMF, next, hHalt output hOutput, PMF.pure_map]) horizon
    (by rw [complete_budget]; exact hBudget)
  simpa only [eval, complete_entry, complete_semantics, PMF.map_comp, Function.comp_def, complete_exit] using hp

/-- Every prefix includes the represented padding and both finite programs. -/
theorem encoded_peak (program : Program) (key payload : List Bool)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (target : ResponseHandoff.Control)
    (hTarget : target ∈ (eval program elapsed (.headerWriting (retainedKey key) payload {})).support) :
    (completeEncoding.encode (PrivateKeyCopy.code, program, target)).length ≤
      bound program (responderPc (.headerWriting (retainedKey key) payload {}))
        (PrivacyStorage.responderCells (.headerWriting (retainedKey key) payload {})) horizon :=
  ResponseHandoffProgram.encoded_peak program horizon elapsed hElapsed _ target hTarget

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Repeated
