import Foundation.Crypto.Semantics.Machine.NativeUniformSequence

/-! Charged native erasure of a fixed number of private history cells while
preserving nearer cells, both physical tape suffixes and the output tape. -/
namespace Machine.NativePrivateHistoryErasure
open Foundation.Probability NativeUniformSequence NativeBitDecisionTree

inductive Action where
  | left | right | erase

def instruction : Action → Instruction
  | .left => .moveLeft .input
  | .right => .moveRight .input
  | .erase => .erase .input

def act : Action → Tape → Tape
  | .left => Tape.moveLeft
  | .right => Tape.moveRight
  | .erase => fun t => t.write none

def atom (a : Action) : Program := [instruction a, .halt]

def applyActions : List Action → Tape → Tape
  | [], t => t
  | a :: rest, t => applyActions rest (act a t)

def code : List Action → Program
  | [] => [.halt]
  | a :: rest => (atom a).followedBy (code rest)

theorem atom_run (a : Action) (input output : Tape) :
    evalConfigWithin (atom a) (NativeBitChoice.start input output) 2 =
      PMF.pure {pc := 1, inputTape := act a input, outputTape := output, halted := true} := by
  cases a <;> simp [atom, instruction, act, evalConfigWithin, stepPMF, next,
    NativeBitChoice.start, Instruction.next, Configuration.advance, Configuration.updateTape]

theorem atom_stops (a : Action) : StopsEverywhere (atom a) 2 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [atom_run, PMF.mem_support_pure_iff] at h
  subst finish
  rfl

theorem code_length (actions : List Action) : (code actions).length = 5 * actions.length + 1 := by
  induction actions with
  | nil => rfl
  | cons a rest ih => simp [code, NativeUniformSequence.code_length, atom, ih]; omega

theorem stops (actions : List Action) : StopsEverywhere (code actions) (3 * actions.length + 1) := by
  induction actions with
  | nil =>
    intro input output finish trace
    have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    have he : evalConfigWithin (code []) (NativeBitChoice.start input output) 1 =
        PMF.pure {pc := 0, inputTape := input, outputTape := output, halted := true} := by
      simp [code, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next]
    change finish ∈ (evalConfigWithin (code []) (NativeBitChoice.start input output) 1).support at h
    rw [he, PMF.mem_support_pure_iff] at h
    subst finish
    rfl
  | cons a rest ih =>
    have h := NativeUniformSequence.stops (atom a) (code rest) 2
      (3 * rest.length + 1) (atom_stops a) ih
    convert h using 1 <;> simp [code] <;> omega

theorem run (actions : List Action) (input output : Tape) :
    evalConfigWithin (code actions) (NativeBitChoice.start input output)
      (3 * actions.length + 1) =
      PMF.pure {pc := (code actions).length - 1, inputTape := applyActions actions input, outputTape := output, halted := true} := by
  induction actions generalizing input with
  | nil =>
    simp [code, applyActions, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next]
  | cons a rest ih =>
    rw [show 3 * (a :: rest).length + 1 = 2 + (3 * rest.length + 1) + 1 by simp; omega]
    rw [code, NativeUniformSequence.run _ _ _ _ (atom_stops a) (stops rest), atom_run,
      PMF.pure_bind]
    change (evalConfigWithin (code rest) (NativeBitChoice.start (act a input) output)
      (3 * rest.length + 1)).map _ = _
    rw [ih, PMF.pure_map]
    congr 1
    simp [applyActions, NativeUniformSequence.code_length, atom]

theorem apply_append (xs ys : List Action) (t : Tape) :
    applyActions (xs ++ ys) t = applyActions ys (applyActions xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih => exact ih (act a t)

def eraseActions : ℕ → List Action
  | 0 => []
  | n + 1 => [.left, .erase] ++ eraseActions n ++ [.right]

def protectedActions : ℕ → ℕ → List Action
  | 0, n => eraseActions n
  | k + 1, n => [.left] ++ protectedActions k n ++ [.right]

theorem erase_length (n : ℕ) : (eraseActions n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eraseActions, ih]; omega

theorem protected_length (k n : ℕ) : (protectedActions k n).length = 2 * k + 3 * n := by
  induction k with
  | zero => simpa only [protectedActions, Nat.mul_zero, Nat.zero_add] using erase_length n
  | succ k ih => simp [protectedActions, ih]; omega

theorem erase_cells (history before : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) :
    applyActions (eraseActions history.length)
      {left := history ++ before, current := current, right := right} =
      {left := List.replicate history.length none ++ before, current := current, right := right} := by
  induction history generalizing current right with
  | nil => rfl
  | cons b history ih =>
    simp only [List.length_cons, eraseActions, apply_append, applyActions, act,
      List.cons_append, Tape.moveLeft, Tape.write]
    rw [ih]
    simp [Tape.moveRight, List.replicate_succ]

theorem protected_cells (keep history before : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) :
    applyActions (protectedActions keep.length history.length)
      {left := keep ++ history ++ before, current := current, right := right} =
      {left := keep ++ List.replicate history.length none ++ before,
        current := current, right := right} := by
  induction keep generalizing current right with
  | nil => exact erase_cells history before current right
  | cons b keep ih =>
    simp only [List.length_cons, protectedActions, apply_append, applyActions, act,
      List.cons_append, Tape.moveLeft]
    rw [ih]
    rfl

def cleanup : Program := code (protectedActions 3 27)

theorem cleanup_stops : StopsEverywhere cleanup 262 := by
  have h := stops (protectedActions 3 27)
  rw [protected_length] at h
  exact h

theorem cleanup_length : cleanup.length = 436 := by
  unfold cleanup
  rw [code_length, protected_length]

end Machine.NativePrivateHistoryErasure
