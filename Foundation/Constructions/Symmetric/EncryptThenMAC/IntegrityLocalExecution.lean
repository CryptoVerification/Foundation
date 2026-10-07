import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityResponse

/-! Local native encryption embedded in the actual integrity controller.
Its ready test is part of the evaluated machine, not an external assumption.
All public/source configurations and histories remain unchanged until the
completed encryption is dispatched to failure or to the signing capability. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

variable (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
  (key used : Bool) (machine : Configuration) (request : List Bool) (state : State)
  (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))

def encryptionBudget (used : Bool) : Nat := 8 + IntegrityEncryption.steps used

def encrypted (key used : Bool) (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool)) : Frame State :=
  ⟨state, .encrypting key used machine request
    (.encrypting (IntegrityEncryption.finish used key (request.headD false))), sourceTrace, signingTrace⟩

/-- Evaluate the actual ready-guarded controller through private packet
preparation and encryption. No signing occurs within this prefix. -/
theorem local_encryption_run :
    eval code oracle (encryptionBudget used)
      ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ =
      PMF.pure (encrypted key used machine request state sourceTrace signingTrace) := by
  cases request with
  | nil =>
    cases used <;> cases key <;>
      simp [eval, TimedExecution.eval, step, transition, nativeAction, next,
        encryptionBudget, encrypted, IntegrityPreparation.initial, IntegrityPreparation.ready,
        IntegrityPreparation.prepareNext, IntegrityEncryption.ready, IntegrityEncryption.finish,
        IntegrityEncryption.steps, OneBitEncryption.Native.encryptionCode,
        Instruction.next, Configuration.initial, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.ofBits,
        Tape.write, Tape.moveRight, Tape.moveLeft]
  | cons message rest =>
    cases used <;> cases key <;> cases message <;>
      simp [eval, TimedExecution.eval, step, transition, nativeAction, next,
      encryptionBudget, encrypted, IntegrityPreparation.initial, IntegrityPreparation.ready,
      IntegrityPreparation.prepareNext, IntegrityEncryption.ready, IntegrityEncryption.finish,
      IntegrityEncryption.steps, OneBitEncryption.Native.encryptionCode,
      Instruction.next, Configuration.initial, Configuration.tape,
      Configuration.updateTape, Configuration.advance, Tape.ofBits,
      Tape.write, Tape.moveRight, Tape.moveLeft]

noncomputable def encryptionBlock :
    TimedExecution.Block (step code oracle)
      ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ :=
  TimedExecution.Block.fixed (step code oracle) (encryptionBudget used) _

theorem encryptionBlock_outcome :
    (encryptionBlock code oracle key used machine request state sourceTrace signingTrace).outcome =
      PMF.pure (encrypted key used machine request state sourceTrace signingTrace, encryptionBudget used) := by
  change (eval code oracle (encryptionBudget used)
    ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩).map _ = _
  rw [local_encryption_run, PMF.pure_map]

def encryptionBoundary (frame : Frame State) : Bool :=
  match frame.control with
  | .encrypting _ _ _ _ control => (IntegrityPreparation.ready control).isSome
  | _ => false

theorem encryptionBlock_completes :
    (encryptionBlock code oracle key used machine request state sourceTrace signingTrace).Completes encryptionBoundary := by
  intro result hResult
  rw [encryptionBlock_outcome, PMF.mem_support_pure_iff] at hResult
  subst result
  cases used <;> rfl

theorem encryptionBudget_le : encryptionBudget used ≤ 20 := by
  exact IntegrityPreparation.budget used

/-- A failed local encryption proceeds through the real failure return.
The external oracle and signing history remain untouched throughout. -/
theorem failed_query_run :
    eval code oracle 21
      ⟨state, .encrypting key true machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ =
      PMF.pure (resumed key machine request [false] state sourceTrace signingTrace) := by
  rw [show 21 = encryptionBudget true + (6 + 1) by rfl,
    eval_add, local_encryption_run, PMF.pure_bind, eval_succ]
  have hStep : step code oracle (encrypted key true machine request state sourceTrace signingTrace) =
      PMF.pure ⟨state, .failure key machine request, sourceTrace, signingTrace⟩ := rfl
  rw [hStep, PMF.pure_bind, failed_response_run]

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
