import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivateKeyCopy
import Foundation.Constructions.Symmetric.EncryptThenMAC.AuthenticateResponse
import Foundation.Crypto.Semantics.Machine.Masking

/-! A private response controller. Key copying uses the actual native code;
the prepared response tape is rewound cell by cell before authentication.
Only the authenticated output is publicly observed. The initial entry point
writes the constant-size response header cell by cell. The retained key tape
is never the authentication output. Key generation remains a caller task. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoff
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive Control where
  | headerWriting : Tape → List Bool → Tape → Control
  | headerAdvancing : Tape → List Bool → Tape → Control
  | copying : Configuration → Control
  | rewinding : Tape → Tape → Control
  | authenticating : Tape → Configuration → Control
  deriving DecidableEq, Repr

def keyStore : Control → Tape
  | .headerWriting key _ _ | .headerAdvancing key _ _ => key
  | .copying machine => machine.inputTape
  | .rewinding key _ | .authenticating key _ => key

/-- This public observation exposes only the authenticated output. It omits
both the retained key store and the signer's private input tape. -/
def publicPacket : Control → Option (List Bool)
  | .authenticating _ machine => if machine.halted then some machine.outputBits else none
  | _ => none

noncomputable def step : Control → PMF Control
  | .headerWriting key remaining buffer =>
      match remaining with
      | [] => PMF.pure (.copying { inputTape := key, outputTape := buffer })
      | bit :: rest => PMF.pure (.headerAdvancing key rest (buffer.write (some bit)))
  | .headerAdvancing key remaining buffer =>
      PMF.pure (.headerWriting key remaining buffer.moveRight)
  | .copying machine =>
      if machine.halted then PMF.pure (.rewinding machine.inputTape machine.outputTape)
      else (stepPMF PrivateKeyCopy.code machine).map .copying
  | .rewinding key buffer =>
      match buffer.left with
      | [] => PMF.pure (.authenticating key { inputTape := buffer })
      | _ :: _ => PMF.pure (.rewinding key buffer.moveLeft)
  | .authenticating key machine =>
      (stepPMF AuthenticateResponse.code machine).map (.authenticating key)

noncomputable def eval : Nat → Control → PMF Control
  | 0, start => PMF.pure start
  | fuel + 1, start => (step start).bind (eval fuel)

theorem eval_add (first second : Nat) (start : Control) :
    eval (first + second) start = (eval first start).bind (eval second) := by
  induction first generalizing start with
  | zero => simp [eval, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, eval, PMF.bind_bind]
      congr 1
      funext next
      exact ih next

theorem authenticate_eval (key : Tape) (machine : Configuration) (fuel : Nat) :
    eval fuel (.authenticating key machine) =
      (evalConfigWithin AuthenticateResponse.code machine fuel).map (.authenticating key) := by
  induction fuel generalizing machine with
  | zero => simp [eval, evalConfigWithin, PMF.pure_map]
  | succ fuel ih =>
      rw [eval, step, PMF.bind_map, evalConfigWithin_succ_head, PMF.map_bind]
      congr 1
      funext next
      exact ih next

def fromCells (cells : List (Option Bool)) : Tape :=
  ⟨[], cells.headD none, cells.tail⟩

/-- Each move of the prepared-buffer head consumes a distinct transition;
the final transition transfers tape ownership to a fresh authentication frame. -/
theorem rewind_eval (left : List Bool) (current : Option Bool) (right : List (Option Bool))
    (key : Tape) :
    eval (left.length + 1) (.rewinding key ⟨left.map some, current, right⟩) =
      PMF.pure (.authenticating key { inputTape := fromCells (left.reverse.map some ++ current :: right) }) := by
  induction left generalizing current right with
  | nil => simp [eval, step, fromCells, PMF.pure_bind]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, eval]
      simp only [step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell cells ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem prepared_equivalent (bits : List Bool) :
    (fromCells (bits.map some ++ [none])).Equivalent (Tape.ofBits bits) := by
  cases bits with
  | nil => exact Tape.Equivalent.refl _
  | cons bit bits => exact ⟨rfl, fun _ => rfl, getD_append_blank (bits.map some)⟩

def header : Option Bool → List Bool
  | none => [false]
  | some bit => [true, bit]

def keyBytes {width : Nat} (key : TableMAC.Key width) : List Bool :=
  Machine.OneTimePad.pairInput key.1.toList key.2.toList

def copied {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : Control :=
  .copying (PrivateKeyCopy.finish (keyBytes key) ((header ciphertext).reverse.map some))

def retainedKey {width : Nat} (key : TableMAC.Key width) : Tape :=
  PrivateKeyCopy.restored ((keyBytes key).map some ++ [none])

def preparedMachine {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : Configuration :=
  { inputTape := fromCells ((header ciphertext ++ keyBytes key).map some ++ [none]) }

theorem copied_to_authentication {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    eval ((keyBytes key).length + (header ciphertext).length + 2) (copied key ciphertext) =
      PMF.pure (.authenticating (retainedKey key) (preparedMachine key ciphertext)) := by
  have hBudget : (keyBytes key).length + (header ciphertext).length + 2 =
      ((header ciphertext ++ keyBytes key).reverse.length + 1) + 1 := by simp
  rw [hBudget, eval]
  simp only [copied, step, PrivateKeyCopy.finish, ↓reduceIte, PMF.pure_bind]
  have hLayout : (keyBytes key).reverse.map some ++ (header ciphertext).reverse.map some =
      (header ciphertext ++ keyBytes key).reverse.map some := by
    simp [List.reverse_append, List.map_append]
  rw [hLayout, rewind_eval]
  simp [retainedKey, preparedMachine, List.map_append]

/-- After the copy, all public observations are exactly the authenticated
response. The physical retained key is preserved jointly with that output. -/
theorem response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (eval ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14))
      (copied key ciphertext)).map (fun final => (keyStore final, publicPacket final)) =
      PMF.pure (retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  rw [eval_add, copied_to_authentication, PMF.pure_bind, authenticate_eval, PMF.map_comp]
  have hConfig : (preparedMachine key ciphertext).Equivalent
      (Configuration.initial (AuthenticateResponse.input key ciphertext)) := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    cases ciphertext with
    | none => simpa [preparedMachine, AuthenticateResponse.input, header, keyBytes, Configuration.initial] using
        prepared_equivalent ([false] ++ keyBytes key)
    | some bit => simpa [preparedMachine, AuthenticateResponse.input, header, keyBytes, Configuration.initial] using
        prepared_equivalent ([true, bit] ++ keyBytes key)
  have hOutput := hConfig.evalOutput AuthenticateResponse.code (8 * width + 14)
  have hSemantic := AuthenticateResponse.realizes_privacy_response (fun _ => width) 0 key ciphertext
  rw [← evalWithin] at hOutput
  rw [hSemantic] at hOutput
  change ((evalConfigWithin AuthenticateResponse.code (preparedMachine key ciphertext) (8 * width + 14)).map
    (fun machine => (retainedKey key, if machine.halted then some machine.outputBits else none))) = _
  have hJoint := congrArg (fun distribution => distribution.map (fun packet => (retainedKey key, packet))) hOutput
  simpa only [PMF.map_comp, PMF.pure_map, Function.comp_def] using hJoint

def StopsWithin (start : Control) (fuel : Nat) : Prop :=
  ∀ final ∈ (eval fuel start).support, (publicPacket final).isSome = true

theorem step_terminal (final : Control) (h : (publicPacket final).isSome = true) :
    step final = PMF.pure final := by
  cases final with
  | headerWriting key remaining buffer => simp [publicPacket] at h
  | headerAdvancing key remaining buffer => simp [publicPacket] at h
  | copying machine => simp [publicPacket] at h
  | rewinding key buffer => simp [publicPacket] at h
  | authenticating key machine =>
      cases hh : machine.halted with
      | false => simp [publicPacket, hh] at h
      | true => simp [step, stepPMF, next, hh, PMF.pure_map]

theorem eval_terminal (fuel : Nat) (final : Control) (h : (publicPacket final).isSome = true) :
    eval fuel final = PMF.pure final := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [eval, step_terminal final h, PMF.pure_bind, ih]

theorem eval_stable (start : Control) (fuel extra : Nat) (h : StopsWithin start fuel) :
    eval (fuel + extra) start = eval fuel start := by
  rw [eval_add, ← PMF.bindOnSupport_eq_bind]
  calc
    (eval fuel start).bindOnSupport (fun final _ => eval extra final) =
        (eval fuel start).bindOnSupport (fun final _ => PMF.pure final) := by
      congr 1
      funext final hFinal
      exact eval_terminal extra final (h final hFinal)
    _ = eval fuel start := PMF.bindOnSupport_pure _

theorem response_stops {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    StopsWithin (copied key ciphertext)
      ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)) := by
  intro final hFinal
  have hm : (keyStore final, publicPacket final) ∈
      ((eval ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14))
        (copied key ciphertext)).map (fun final => (keyStore final, publicPacket final))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨final, hFinal, rfl⟩
  rw [response_run, PMF.mem_support_pure_iff] at hm
  have hp := congrArg Prod.snd hm
  dsimp only at hp
  rw [hp]
  rfl

theorem copying_runs {start final : Configuration} {used : Nat}
    (run : RunsFor PrivateKeyCopy.code start final used) :
    eval used (.copying start) = PMF.pure (.copying final) := by
  have hNoRandom : ∀ tape, Instruction.randomBit tape ∉ PrivateKeyCopy.code := by
    intro tape
    cases tape <;> decide
  induction used generalizing start with
  | zero => cases run; rfl
  | succ used ih =>
      obtain ⟨middle, first, rest⟩ := run.head
      have hActive : start.halted = false := by
        cases hh : start.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted hh) first)
      rw [eval, step, hActive]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [stepPMF_eq_pure_of_no_randomBit hNoRandom first, PMF.pure_map, PMF.pure_bind]
      exact ih rest

def starting {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : Control :=
  .copying (PrivateKeyCopy.copying [] (keyBytes key) ((header ciphertext).reverse.map some))

/-- Complete execution from the start of native copying, not just a
postulated copied buffer. The head traversal and stage change are included. -/
theorem full_response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (eval ((8 * (keyBytes key).length + 5) +
      ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)))
      (starting key ciphertext)).map (fun final => (keyStore final, publicPacket final)) =
      PMF.pure (retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  let budget := 8 * (keyBytes key).length + 5
  let responseBudget := (keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)
  have hNative : PrivateKeyCopy.finish (keyBytes key) ((header ciphertext).reverse.map some) ∈
      (evalConfigWithin PrivateKeyCopy.code
        (PrivateKeyCopy.copying [] (keyBytes key) ((header ciphertext).reverse.map some)) budget).support := by
    rw [PrivateKeyCopy.run, PMF.mem_support_pure_iff]
  have hPadded := (mem_support_evalConfigWithin_iff _ _ _ _).mp hNative
  obtain ⟨used, hUsed, actual⟩ := hPadded.toRunsFor_le
  have hCopy := copying_runs actual
  have hBudget : budget + responseBudget = used + (responseBudget + (budget - used)) := by omega
  change (eval (budget + responseBudget) (starting key ciphertext)).map _ = _
  rw [hBudget, eval_add]
  unfold starting
  rw [hCopy, PMF.pure_bind]
  change (eval (responseBudget + (budget - used)) (copied key ciphertext)).map _ = _
  rw [eval_stable _ responseBudget (budget - used) (response_stops key ciphertext)]
  exact response_run key ciphertext

theorem full_response_stops {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    StopsWithin (starting key ciphertext) ((8 * (keyBytes key).length + 5) +
      ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14))) := by
  intro final hFinal
  have hm : (keyStore final, publicPacket final) ∈
      ((eval ((8 * (keyBytes key).length + 5) +
        ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)))
        (starting key ciphertext)).map (fun final => (keyStore final, publicPacket final))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨final, hFinal, rfl⟩
  rw [full_response_run, PMF.mem_support_pure_iff] at hm
  have hp := congrArg Prod.snd hm
  dsimp only at hp
  rw [hp]
  rfl

/-- Executable path interpreter with the same cell-level stage transitions.
Both native routines are deterministic, so the supplied native coin is unused. -/
def simulateStep : Control → Control
  | .headerWriting key remaining buffer =>
      match remaining with
      | [] => .copying { inputTape := key, outputTape := buffer }
      | bit :: rest => .headerAdvancing key rest (buffer.write (some bit))
  | .headerAdvancing key remaining buffer => .headerWriting key remaining buffer.moveRight
  | .copying machine =>
      if machine.halted then .rewinding machine.inputTape machine.outputTape
      else .copying (Masking.nativeNext PrivateKeyCopy.code machine false)
  | .rewinding key buffer =>
      match buffer.left with
      | [] => .authenticating key { inputTape := buffer }
      | _ :: _ => .rewinding key buffer.moveLeft
  | .authenticating key machine =>
      .authenticating key (Masking.nativeNext AuthenticateResponse.code machine false)

private theorem native_mem_support (code : Program) (machine : Configuration) :
    Masking.nativeNext code machine false ∈ (stepPMF code machine).support := by
  have hm := Masking.simulateStep_mem_support (.native code) false (.running machine)
  change Masking.Configuration.running (Masking.nativeNext code machine false) ∈
    ((stepPMF code machine).map Masking.Configuration.running).support at hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨final, hFinal, hEq⟩ := hm
  have he : final = Masking.nativeNext code machine false := by cases hEq; rfl
  rw [← he]
  exact hFinal

theorem simulateStep_mem_support (start : Control) : simulateStep start ∈ (step start).support := by
  cases start with
  | headerWriting key remaining buffer => cases remaining <;> simp [simulateStep, step]
  | headerAdvancing key remaining buffer => simp [simulateStep, step]
  | copying machine =>
      cases hh : machine.halted with
      | true => simp [simulateStep, step, hh]
      | false =>
          simp only [simulateStep, step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff]
          exact ⟨_, native_mem_support _ _, rfl⟩
  | rewinding key buffer =>
      cases hl : buffer.left <;> simp [simulateStep, step, hl]
  | authenticating key machine =>
      simp only [simulateStep, step, PMF.mem_support_map_iff]
      exact ⟨_, native_mem_support _ _, rfl⟩

def simulate : Nat → Control → Control × Nat
  | 0, start => (start, 0)
  | fuel + 1, start =>
      if (publicPacket start).isSome then (start, 0)
      else let result := simulate fuel (simulateStep start)
           (result.1, result.2 + 1)

theorem simulate_mem_support (fuel : Nat) (start : Control) :
    (simulate fuel start).1 ∈ (eval fuel start).support := by
  induction fuel generalizing start with
  | zero => simp [simulate, eval]
  | succ fuel ih =>
      by_cases h : (publicPacket start).isSome = true
      · rw [eval_terminal (fuel + 1) start h]
        simp [simulate, h]
      · simp only [simulate, h, ↓reduceIte, eval, PMF.mem_support_bind_iff]
        exact ⟨simulateStep start, simulateStep_mem_support start, ih _⟩

theorem header_eval (key : Tape) (remaining : List Bool) (before : List (Option Bool)) :
    eval (2 * remaining.length + 1) (.headerWriting key remaining { left := before }) =
      PMF.pure (.copying { inputTape := key, outputTape := { left := remaining.reverse.map some ++ before } }) := by
  induction remaining generalizing before with
  | nil => simp [eval, step, PMF.pure_bind]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega, eval]
      simp only [step, Tape.write, PMF.pure_bind]
      rw [eval, step]
      simp only [PMF.pure_bind, Tape.moveRight]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- This entry point writes the response header cell by cell. The only input
precondition is an existing private key store, which key generation supplies. -/
def initial {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : Control :=
  .headerWriting (Tape.ofBits (keyBytes key)) (header ciphertext) {}

theorem initial_to_copy {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    eval (2 * (header ciphertext).length + 1) (initial key ciphertext) =
      PMF.pure (starting key ciphertext) := by
  unfold initial
  rw [header_eval]
  simp only [List.append_nil]
  have hStart : ({ inputTape := Tape.ofBits (keyBytes key), outputTape := { left := (header ciphertext).reverse.map some } } : Configuration) =
      PrivateKeyCopy.copying [] (keyBytes key) ((header ciphertext).reverse.map some) := by
    cases keyBytes key <;> rfl
  rw [hStart]
  rfl

theorem initial_response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (eval ((2 * (header ciphertext).length + 1) + (8 * (keyBytes key).length + 5) +
      ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)))
      (initial key ciphertext)).map (fun final => (keyStore final, publicPacket final)) =
      PMF.pure (retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  rw [Nat.add_assoc, eval_add, initial_to_copy, PMF.pure_bind]
  exact full_response_run key ciphertext

theorem keyBytes_length {width : Nat} (key : TableMAC.Key width) : (keyBytes key).length = 2 * width := by
  rw [keyBytes, Machine.OneTimePad.pairInput_length _ _ (by simp)]
  simp

def budget (width : Nat) (ciphertext : Option Bool) : Nat :=
  26 * width + 3 * (header ciphertext).length + 22

theorem bounded_response_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (eval (budget width ciphertext) (initial key ciphertext)).map
      (fun final => (keyStore final, publicPacket final)) =
      PMF.pure (retainedKey key, some (AuthenticateResponse.encode
        (authenticate OneBitEncryption.scheme (TableMAC.scheme (fun _ => width)) 0 key ciphertext))) := by
  have hBudget : budget width ciphertext =
      (2 * (header ciphertext).length + 1) + (8 * (keyBytes key).length + 5) +
        ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14)) := by
    rw [keyBytes_length]
    unfold budget
    omega
  rw [hBudget]
  exact initial_response_run key ciphertext

theorem initial_stops {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    StopsWithin (initial key ciphertext) (budget width ciphertext) := by
  intro final hFinal
  have hm : (keyStore final, publicPacket final) ∈
      ((eval (budget width ciphertext) (initial key ciphertext)).map
        (fun final => (keyStore final, publicPacket final))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨final, hFinal, rfl⟩
  rw [bounded_response_run, PMF.mem_support_pure_iff] at hm
  have hp := congrArg Prod.snd hm
  dsimp only at hp
  rw [hp]
  rfl

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoff
