import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivateKeyGeneration

/-! Use the physical key store returned by native generation in the native
response controller. The trailing blank cell is retained and consumed by the
copy routine, not removed by a host-side tape normalization. -/
namespace Foundation.Symmetric.EncryptThenMAC.GeneratedResponse
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def copying (before remaining : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { inputTape := { ResponseHandoff.fromCells (remaining.map some ++ [none]) with left := before.reverse.map some },
    outputTape := { left := outputBefore } }

theorem copy_cell (bit : Bool) (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying before (bit :: remaining) outputBefore) 6 =
      PMF.pure (copying (before ++ [bit]) remaining (some bit :: outputBefore)) := by
  cases bit <;> cases remaining <;>
    simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, copying, ResponseHandoff.fromCells,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight, List.reverse_append]

theorem copy_loop (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying before remaining outputBefore) (6 * remaining.length + 1) =
      PMF.pure (PrivateKeyCopy.rewinding (before ++ remaining).reverse none []
        { left := remaining.reverse.map some ++ outputBefore }) := by
  induction remaining generalizing before outputBefore with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, PrivateKeyCopy.code, copying, ResponseHandoff.fromCells,
        PrivateKeyCopy.rewinding, Instruction.next, Configuration.tape]
  | cons bit remaining ih =>
      rw [show 6 * (bit :: remaining).length + 1 = 6 + (6 * remaining.length + 1) by simp; omega,
        evalConfigWithin_add, copy_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem copy_run (key : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin PrivateKeyCopy.code (copying [] key outputBefore) (8 * key.length + 5) =
      PMF.pure (PrivateKeyCopy.finish key outputBefore) := by
  rw [show 8 * key.length + 5 = (6 * key.length + 1) + (2 * key.reverse.length + 4) by simp; omega,
    evalConfigWithin_add, copy_loop, PMF.pure_bind]
  simpa [PrivateKeyCopy.finish] using PrivateKeyCopy.rewind_loop key.reverse none []
    ({ left := key.reverse.map some ++ outputBefore } : Tape)

def startCopy {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : ResponseHandoff.Control :=
  .copying (copying [] (ResponseHandoff.keyBytes key) ((ResponseHandoff.header ciphertext).reverse.map some))

theorem copied_response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval ((8 * (ResponseHandoff.keyBytes key).length + 5) +
      ((ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14)))
      (startCopy key ciphertext)).map (fun final => (ResponseHandoff.keyStore final, ResponseHandoff.publicPacket final)) =
      PMF.pure (ResponseHandoff.retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  let budget := 8 * (ResponseHandoff.keyBytes key).length + 5
  let responseBudget := (ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14)
  have hNative : PrivateKeyCopy.finish (ResponseHandoff.keyBytes key) ((ResponseHandoff.header ciphertext).reverse.map some) ∈
      (evalConfigWithin PrivateKeyCopy.code
        (copying [] (ResponseHandoff.keyBytes key) ((ResponseHandoff.header ciphertext).reverse.map some)) budget).support := by
    rw [copy_run, PMF.mem_support_pure_iff]
  have hPadded := (mem_support_evalConfigWithin_iff _ _ _ _).mp hNative
  obtain ⟨used, hUsed, actual⟩ := hPadded.toRunsFor_le
  have hCopy := ResponseHandoff.copying_runs actual
  have hBudget : budget + responseBudget = used + (responseBudget + (budget - used)) := by omega
  change (ResponseHandoff.eval (budget + responseBudget) (startCopy key ciphertext)).map _ = _
  rw [hBudget, ResponseHandoff.eval_add]
  unfold startCopy
  rw [hCopy, PMF.pure_bind]
  change (ResponseHandoff.eval (responseBudget + (budget - used)) (ResponseHandoff.copied key ciphertext)).map _ = _
  rw [ResponseHandoff.eval_stable _ responseBudget (budget - used) (ResponseHandoff.response_stops key ciphertext)]
  exact ResponseHandoff.response_run key ciphertext

def initial {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : ResponseHandoff.Control :=
  .headerWriting (PrivateKeyGeneration.store key) (ResponseHandoff.header ciphertext) {}

theorem response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (ResponseHandoff.eval (ResponseHandoff.budget width ciphertext) (initial key ciphertext)).map
      (fun final => (ResponseHandoff.keyStore final, ResponseHandoff.publicPacket final)) =
      PMF.pure (ResponseHandoff.retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  have hBudget : ResponseHandoff.budget width ciphertext =
      (2 * (ResponseHandoff.header ciphertext).length + 1) +
        ((8 * (ResponseHandoff.keyBytes key).length + 5) +
          ((ResponseHandoff.keyBytes key).length + (ResponseHandoff.header ciphertext).length + 2 + (8 * width + 14))) := by
    rw [ResponseHandoff.keyBytes_length]
    unfold ResponseHandoff.budget
    omega
  rw [hBudget, ResponseHandoff.eval_add]
  unfold initial
  rw [ResponseHandoff.header_eval, PMF.pure_bind]
  simp only [List.append_nil]
  change (ResponseHandoff.eval _ (startCopy key ciphertext)).map _ = _
  exact copied_response_run key ciphertext

/-- Sequential execution of the two proved finite stages. The generated tape
is passed directly to the response controller. This describes one local
initialization/response experiment; repeated queries must retain the key. -/
noncomputable def generateAndRespond (width : Nat) (ciphertext : Option Bool) :
    PMF (Option (Tape × Option (List Bool))) :=
  (PrivateKeyGeneration.eval (12 * width + 4)
    (PrivateKeyGeneration.initial (List.replicate (2 * width) true))).bind fun generated =>
      match PrivateKeyGeneration.readyStore generated with
      | none => PMF.pure none
      | some tape =>
          (ResponseHandoff.eval (ResponseHandoff.budget width ciphertext)
            (.headerWriting tape (ResponseHandoff.header ciphertext) {})).map
              (fun final => some (ResponseHandoff.keyStore final, ResponseHandoff.publicPacket final))

theorem generateAndRespond_run (width : Nat) (ciphertext : Option Bool) :
    generateAndRespond width ciphertext =
      ((TableMAC.scheme (fun _ => width)).keygen 0).map (fun key =>
        some (ResponseHandoff.retainedKey key, some (AuthenticateResponse.encode
          (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext)))) := by
  unfold generateAndRespond
  rw [PrivateKeyGeneration.table_key_run (fun _ => width) 0, PMF.bind_map]
  simp only [Function.comp_def, PrivateKeyGeneration.readyStore]
  rw [PMF.map]
  congr 1
  funext key
  have h := congrArg (fun distribution => distribution.map some) (response_run key ciphertext)
  simpa only [initial, PMF.map_comp, PMF.pure_map, Function.comp_def] using h

end Foundation.Symmetric.EncryptThenMAC.GeneratedResponse
