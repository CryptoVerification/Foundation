import Foundation.Crypto.Semantics.Oracle.LeftBlankRewind

/-! Runtime fuel stored left of a blank table boundary. Consumed cells are
false, remaining cells true. Consumption changes one real cell and returns to
the table; code size does not depend on initial or remaining fuel. -/
namespace CryptoOracle.Interactive.UnaryFuel
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def counterWith (savedContext : List (Option Bool)) (fuel used : Nat) : List (Option Bool) :=
  List.replicate used (some false) ++ List.replicate fuel (some true) ++ none :: savedContext

def counter (fuel used : Nat) : List (Option Bool) := counterWith [] fuel used

def tapeWith (savedContext : List (Option Bool)) (fuel used : Nat) (table : List (Option Bool)) : Tape :=
  FixedWidthCopy.frontier (none :: counterWith savedContext fuel used) table

def tape (fuel used : Nat) (table : List (Option Bool)) : Tape :=
  tapeWith [] fuel used table

theorem counterWith_eq_append (savedContext : List (Option Bool)) (fuel used : Nat) :
    counterWith savedContext fuel used = counter fuel used ++ savedContext := by
  simp [counterWith, counter, List.append_assoc]

def body (empty : Nat) : Code :=
  [.native (.moveLeft .input), .native (.moveLeft .input),
   .native (.branch .input empty 3 5), .native (.moveLeft .input), .native (.jump 2),
   .native (.write .input false), .native (.moveRight .input),
   .native (.branch .input 10 8 8), .native (.moveRight .input), .native (.jump 7),
   .native (.moveRight .input)]

def code (next empty : Code) : Code :=
  CodeRelocation.host (body (11 + next.length)) (CodeRelocation.host next empty)

theorem body_length (empty : Nat) : (body empty).length = 11 := rfl

def cursor (pc : Nat) (input output : Tape) : Machine.Configuration :=
  { pc := pc, inputTape := input, outputTape := output }

theorem replicate_push (used : Nat) (cell : Option Bool) (right : List (Option Bool)) :
    List.replicate used cell ++ cell :: right = cell :: List.replicate used cell ++ right := by
  induction used with
  | zero => rfl
  | succ used ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (cell :: ·) ih

theorem left_cell (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (right left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) 3
      (NativeCode.frame state trace (cursor 2 (FixedWidthCopy.backwardFrontier right (some false :: left)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 2 (FixedWidthCopy.backwardFrontier (some false :: right) left) output)) := by
  cases left <;>
    simp [code, body, cursor, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
      Tape.moveLeft]

theorem left_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (used : Nat) (right left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) (3 * used)
      (NativeCode.frame state trace (cursor 2 (FixedWidthCopy.backwardFrontier right
        (List.replicate used (some false) ++ left)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 2 (FixedWidthCopy.backwardFrontier
        (List.replicate used (some false) ++ right) left) output)) := by
  induction used generalizing right with
  | zero => simp [TimedExecution.eval]
  | succ used ih =>
      rw [show 3 * (used + 1) = 3 + 3 * used from by omega, TimedExecution.eval_add]
      simp only [List.replicate_succ, List.cons_append]
      rw [left_cell, PMF.pure_bind, ih]
      rw [replicate_push]
      rfl

theorem right_cell (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (right left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) 3
      (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier left (some false :: right)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier (some false :: left) right) output)) := by
  cases right <;>
    simp [code, body, cursor, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells, Tape.moveRight]

theorem right_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (used : Nat) (right left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) (3 * used)
      (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier left
        (List.replicate used (some false) ++ right)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier
        (List.replicate used (some false) ++ left) right) output)) := by
  induction used generalizing left with
  | zero => simp [TimedExecution.eval]
  | succ used ih =>
      rw [show 3 * (used + 1) = 3 + 3 * used from by omega, TimedExecution.eval_add]
      simp only [List.replicate_succ, List.cons_append]
      rw [right_cell, PMF.pure_bind, ih]
      rw [replicate_push]
      rfl

section SavedContext
variable {savedContext : List (Option Bool)}
local notation "counter" => counterWith savedContext
local notation "tape" => tapeWith savedContext

theorem prepare_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (fuel used : Nat) (head : Option Bool) (table : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) 2
      (NativeCode.frame state trace (cursor 0 (tape fuel used (head :: table)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 2
        (FixedWidthCopy.backwardFrontier (none :: head :: table) (counter fuel used)) output)) := by
  cases used <;> cases fuel <;>
    simp [code, body, cursor, tapeWith, counterWith, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
      FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveLeft, List.replicate_succ]

theorem consume_cell (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (right left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) 3
      (NativeCode.frame state trace (cursor 2 (FixedWidthCopy.backwardFrontier right (some true :: left)) output)) =
      PMF.pure (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier (some false :: left) right) output)) := by
  cases left <;> cases right <;>
    simp [code, body, cursor, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
      FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight, Tape.write]

theorem finish_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (head : Option Bool) (table left : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) 2
      (NativeCode.frame state trace (cursor 7 (FixedWidthCopy.frontier left (none :: head :: table)) output)) =
      PMF.pure (CodeRelocation.frame 11
        (NativeCode.frame state trace (cursor 0 (FixedWidthCopy.frontier (none :: left) (head :: table)) output))) := by
  simp [code, body, cursor, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, Machine.Instruction.next, Machine.Configuration.advance,
    Machine.Configuration.updateTape, Machine.Configuration.tape,
    FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight,
    CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

theorem consume_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (fuel used : Nat) (head : Option Bool) (table : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) (6 * used + 7)
      (NativeCode.frame state trace (cursor 0 (tape (fuel + 1) used (head :: table)) output)) =
      PMF.pure (CodeRelocation.frame 11
        (NativeCode.frame state trace (cursor 0 (tape fuel (used + 1) (head :: table)) output))) := by
  rw [show 6 * used + 7 = 2 + (3 * used + (3 + (3 * used + 2))) from by omega,
    TimedExecution.eval_add, prepare_run, PMF.pure_bind]
  simp only [counterWith, List.replicate_succ, List.cons_append, List.append_assoc]
  rw [TimedExecution.eval_add, left_run, PMF.pure_bind, TimedExecution.eval_add,
    consume_cell, PMF.pure_bind]
  rw [TimedExecution.eval_add, right_run, PMF.pure_bind, finish_run]
  simp only [tapeWith, counterWith, List.replicate_succ, List.cons_append, List.append_assoc]
  rw [replicate_push]
  rfl

theorem empty_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (next empty : Code)
    (used : Nat) (head : Option Bool) (table : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code next empty) oracle) (3 * used + 3)
      (NativeCode.frame state trace (cursor 0 (tape 0 used (head :: table)) output)) =
      PMF.pure (CodeRelocation.frame (11 + next.length)
        (NativeCode.frame state trace (cursor 0
          { left := savedContext, current := none, right := List.replicate used (some false) ++ none :: head :: table } output))) := by
  rw [show 3 * used + 3 = 2 + (3 * used + 1) from by omega,
    TimedExecution.eval_add, prepare_run, PMF.pure_bind]
  simp only [counterWith, List.replicate_zero, List.append_nil]
  rw [TimedExecution.eval_add, left_run, PMF.pure_bind]
  simp [code, body, cursor, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, Machine.Instruction.next, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
    CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

end SavedContext

theorem code_native (next empty : Code)
    (hn : ∀ op ∈ next, ∃ native, op = .native native)
    (he : ∀ op ∈ empty, ∃ native, op = .native native) :
    ∀ op ∈ code next empty, ∃ native, op = .native native := by
  apply CodeRelocation.host_native
  · intro op hm
    simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · exact CodeRelocation.host_native _ _ hn he

end CryptoOracle.Interactive.UnaryFuel
