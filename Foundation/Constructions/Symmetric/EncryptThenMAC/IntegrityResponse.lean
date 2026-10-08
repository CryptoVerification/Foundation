import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityMachine

/-! Full physical response assembly and return, for arbitrary tag lengths.
All copying and traversal transitions are counted; source resumption is an
intermediate boundary at which normal source execution can continue. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
  (key : Bool) (machine : Configuration) (request : List Bool) (state : State)
  (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))

def resumed (key : Bool) (machine : Configuration) (request response : List Bool)
    (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) : Frame State :=
  ⟨state, .source key true (.loading machine response {}), (request, response) :: sourceTrace, signingTrace⟩

theorem reversing_run (remaining response : List Bool) :
    eval code oracle (remaining.length + 1)
      ⟨state, .reversing key machine request remaining response, sourceTrace, signingTrace⟩ =
      PMF.pure (resumed key machine request (remaining.reverse ++ response) state sourceTrace signingTrace) := by
  induction remaining generalizing response with
  | nil => simp [eval, TimedExecution.eval, step, transition, resumed]
  | cons bit remaining ih =>
      rw [List.length_cons, eval_succ]
      simp only [step, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def fromCells : List (Option Bool) → Tape
  | [] => {}
  | cell :: rest => { current := cell, right := rest }

def buffer (before : List (Option Bool)) (remaining : List Bool) : Tape :=
  { fromCells (remaining.map some ++ [none]) with left := before }

theorem collecting_run (remaining reversed : List Bool) (before : List (Option Bool)) :
    eval code oracle (remaining.length + 1)
      ⟨state, .collecting key machine request (buffer before remaining) reversed, sourceTrace, signingTrace⟩ =
      PMF.pure ⟨state, .reversing key machine request (remaining.reverse ++ reversed) [], sourceTrace, signingTrace⟩ := by
  induction remaining generalizing before reversed with
  | nil => simp [eval, TimedExecution.eval, step, transition, buffer, fromCells]
  | cons bit remaining ih =>
      rw [List.length_cons, eval_succ]
      simp only [step, transition, buffer, fromCells, List.map_cons, List.cons_append, PMF.pure_bind]
      have hMove : ({ left := before, current := some bit, right := remaining.map some ++ [none] } : Tape).moveRight =
          buffer (some bit :: before) remaining := by
        cases remaining <;> rfl
      rw [hMove, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem rewinding_run (left : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    eval code oracle (left.length + 1)
      ⟨state, .rewinding key machine request ⟨left.map some, current, right⟩, sourceTrace, signingTrace⟩ =
      PMF.pure ⟨state, .collecting key machine request
        (fromCells (left.reverse.map some ++ current :: right)) [], sourceTrace, signingTrace⟩ := by
  induction left generalizing current right with
  | nil => simp [eval, TimedExecution.eval, step, transition, fromCells]
  | cons bit left ih =>
      rw [List.length_cons, eval_succ]
      simp only [step, transition, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem return_response_run (response : List Bool) :
    eval code oracle (3 * response.length + 3)
      ⟨state, .rewinding key machine request { left := response.reverse.map some }, sourceTrace, signingTrace⟩ =
      PMF.pure (resumed key machine request response state sourceTrace signingTrace) := by
  rw [show 3 * response.length + 3 = (response.reverse.length + 1) +
      ((response.length + 1) + (response.reverse.length + 1)) by simp; omega,
    eval_add, rewinding_run, PMF.pure_bind]
  simp only [List.reverse_reverse]
  have hBuffer : fromCells (response.map some ++ [none]) = buffer [] response := by
    cases response <;> rfl
  rw [hBuffer]
  change eval code oracle _ ⟨state, .collecting key machine request (buffer [] response) [], sourceTrace, signingTrace⟩ = _
  rw [eval_add, collecting_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reversing_run]
  simp

theorem copying_run (remaining before : List Bool) :
    eval code oracle (2 * remaining.length + 1)
      ⟨state, .copying key machine request remaining { left := before.map some }, sourceTrace, signingTrace⟩ =
      PMF.pure ⟨state, .rewinding key machine request
        { left := (remaining.reverse ++ before).map some }, sourceTrace, signingTrace⟩ := by
  induction remaining generalizing before with
  | nil => simp [eval, TimedExecution.eval, step, transition]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = (2 * remaining.length + 1) + 1 + 1 by simp; omega,
        eval_succ]
      simp only [step, transition, PMF.pure_bind]
      rw [eval_succ]
      simp only [step, transition, Tape.write, Tape.moveRight, PMF.pure_bind]
      change eval code oracle (2 * remaining.length + 1)
        ⟨state, .copying key machine request remaining { left := (bit :: before).map some }, sourceTrace, signingTrace⟩ = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem header_run (ciphertext : Bool) (tag : List Bool) :
    eval code oracle 4
      ⟨state, .header key machine request ciphertext tag 0 {}, sourceTrace, signingTrace⟩ =
      PMF.pure ⟨state, .copying key machine request tag
        { left := [some ciphertext, some true] }, sourceTrace, signingTrace⟩ := by
  simp [eval, TimedExecution.eval, step, transition, Tape.write, Tape.moveRight]

/-- Exact assembly and return budget from a received tag, including empty
tags. No assumption about the oracle or source program is required. -/
theorem signed_response_run (ciphertext : Bool) (tag : List Bool) :
    eval code oracle (5 * tag.length + 14)
      ⟨state, .header key machine request ciphertext tag 0 {}, sourceTrace, signingTrace⟩ =
      PMF.pure (resumed key machine request (true :: ciphertext :: tag) state sourceTrace signingTrace) := by
  rw [show 5 * tag.length + 14 = 4 + ((2 * tag.length + 1) + (3 * (true :: ciphertext :: tag).length + 3)) by simp; omega,
    eval_add, header_run, PMF.pure_bind, eval_add]
  change (eval code oracle (2 * tag.length + 1)
    ⟨state, .copying key machine request tag { left := ([ciphertext, true] : List Bool).map some }, sourceTrace, signingTrace⟩).bind _ = _
  rw [copying_run, PMF.pure_bind]
  have hLeft : (tag.reverse ++ [ciphertext, true]).map some = (true :: ciphertext :: tag).reverse.map some := by
    simp [List.reverse_cons, List.append_assoc]
  rw [hLeft, return_response_run]

theorem failed_response_run :
    eval code oracle 6 ⟨state, .failure key machine request, sourceTrace, signingTrace⟩ =
      PMF.pure (resumed key machine request [false] state sourceTrace signingTrace) := by
  simp [eval, TimedExecution.eval, step, transition, Tape.write, Tape.moveRight, resumed]

/-- The response boundary is not a halt: with additional fuel, execution
continues from the suspended source machine with exactly the unused budget. -/
theorem signed_response_continue (ciphertext : Bool) (tag : List Bool) (extra : Nat) :
    eval code oracle (5 * tag.length + 14 + extra)
      ⟨state, .header key machine request ciphertext tag 0 {}, sourceTrace, signingTrace⟩ =
      eval code oracle extra (resumed key machine request (true :: ciphertext :: tag) state sourceTrace signingTrace) := by
  rw [eval_add, signed_response_run, PMF.pure_bind]

/-- A real execution block that can be composed with signing and source
execution. Its law continues the original machine with the remaining fuel. -/
noncomputable def signedResponseBlock (ciphertext : Bool) (tag : List Bool) :
    TimedExecution.Block (step code oracle)
      ⟨state, .header key machine request ciphertext tag 0 {}, sourceTrace, signingTrace⟩ :=
  TimedExecution.Block.fixed (step code oracle) (5 * tag.length + 14) _

theorem signedResponseBlock_outcome (ciphertext : Bool) (tag : List Bool) :
    (signedResponseBlock code oracle key machine request state sourceTrace signingTrace ciphertext tag).outcome =
      PMF.pure (resumed key machine request (true :: ciphertext :: tag) state sourceTrace signingTrace,
        5 * tag.length + 14) := by
  change (eval code oracle (5 * tag.length + 14)
    ⟨state, .header key machine request ciphertext tag 0 {}, sourceTrace, signingTrace⟩).map _ = _
  rw [signed_response_run, PMF.pure_map]

def sourceBoundary (frame : Frame State) : Bool :=
  match frame.control with
  | .source _ _ _ => true
  | _ => false

theorem signedResponseBlock_completes (ciphertext : Bool) (tag : List Bool) :
    (signedResponseBlock code oracle key machine request state sourceTrace signingTrace ciphertext tag).Completes
      sourceBoundary := by
  intro result hResult
  rw [signedResponseBlock_outcome, PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
