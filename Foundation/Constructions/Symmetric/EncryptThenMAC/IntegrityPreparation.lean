import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncryption
import Foundation.Crypto.Semantics.TimedExecution

/-! Preparing a private three-cell encryption packet is charged explicitly.
Every preparation transition writes one cell, moves one head, or transfers
ownership to the native primitive. No preloaded packet is granted for free. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityPreparation
open Foundation.Probability Machine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

inductive Control where
  | preparing : Nat → Tape → Control
  | encrypting : Configuration → Control
  deriving DecidableEq, Repr

def initial : Control := .preparing 0 {}

def prepareNext (used key message : Bool) (phase : Nat) (tape : Tape) : Control :=
  match phase with
    | 0 => .preparing 1 (tape.write (some used))
    | 1 => .preparing 2 tape.moveRight
    | 2 => .preparing 3 (tape.write (some key))
    | 3 => .preparing 4 tape.moveRight
    | 4 => .preparing 5 (tape.write (some message))
    | 5 => .preparing 6 tape.moveLeft
    | 6 => .preparing 7 tape.moveLeft
    | _ => .encrypting { inputTape := tape }

noncomputable def step (used key message : Bool) : Control → PMF Control
  | .preparing phase tape => PMF.pure (prepareNext used key message phase tape)
  | .encrypting machine => (stepPMF OneBitEncryption.Native.encryptionCode machine).map Control.encrypting

noncomputable def eval (used key message : Bool) := TimedExecution.eval (step used key message)

theorem preparation (used key message : Bool) :
    eval used key message 8 initial =
      PMF.pure (.encrypting (Configuration.initial [used, key, message])) := by
  simp [eval, TimedExecution.eval, step, prepareNext, initial, Tape.write, Tape.moveRight,
    Tape.moveLeft, Configuration.initial, Tape.ofBits]

theorem encrypting_eval (used key message : Bool) (machine : Configuration) (fuel : Nat) :
    eval used key message fuel (.encrypting machine) =
      (evalConfigWithin OneBitEncryption.Native.encryptionCode machine fuel).map Control.encrypting := by
  induction fuel with
  | zero => simp [eval, TimedExecution.eval, evalConfigWithin, PMF.pure_map]
  | succ fuel ih =>
      unfold eval at ih
      change TimedExecution.eval (step used key message) (fuel + 1) (.encrypting machine) = _
      rw [TimedExecution.eval_add, ih]
      simp only [PMF.bind_map, TimedExecution.eval, PMF.bind_pure,
        Function.comp_def, step, ← PMF.map_bind, evalConfigWithin]

theorem encryption (used key message : Bool) :
    eval used key message (8 + IntegrityEncryption.steps used) initial =
      PMF.pure (.encrypting (IntegrityEncryption.finish used key message)) := by
  rw [eval, TimedExecution.eval_add]
  change (eval used key message 8 initial).bind
    (eval used key message (IntegrityEncryption.steps used)) = _
  rw [preparation, PMF.pure_bind, encrypting_eval,
    IntegrityEncryption.encryption_configuration, PMF.pure_map]

def ready : Control → Option (Bool × Option Bool)
  | .preparing _ _ => none
  | .encrypting machine => IntegrityEncryption.ready machine

theorem encryption_result (n : Nat) (used key message : Bool) :
    (eval used key message (8 + IntegrityEncryption.steps used) initial).map ready =
      PMF.pure (some (OneBitEncryption.scheme.encrypt n key used message)) := by
  rw [encryption, PMF.pure_map]
  exact congrArg PMF.pure (IntegrityEncryption.ready_finish n used key message)

theorem budget (used : Bool) : 8 + IntegrityEncryption.steps used ≤ 20 := by
  have h := IntegrityEncryption.steps_le used
  omega

end Foundation.Symmetric.EncryptThenMAC.IntegrityPreparation
