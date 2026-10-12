import Foundation.Crypto.Semantics.Oracle.LeftBlankRewind

/-! Compare an output field with a fixed public bit string. A mismatch is
restored by a real left scan, so both tapes are retained for the next handler. -/
namespace CryptoOracle.Interactive.ForwardConstantCheck
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def cell (fault : Nat) (bit : Bool) : Code :=
  [.native (.branch .output fault (if bit then fault else 1) (if bit then 1 else fault)),
   .native (.moveRight .output)]

def compareCode (fault : Nat) (tail : Code) : List Bool → Code
  | [] => tail
  | bit :: rest => CodeRelocation.host (cell (fault + 2 * rest.length + 2) bit) (compareCode fault tail rest)

theorem compareCode_length (fault : Nat) (tail : Code) (bits : List Bool) :
    (compareCode fault tail bits).length = 2 * bits.length + tail.length := by
  induction bits with
  | nil => simp [compareCode]
  | cons bit rest ih => simp [compareCode, CodeRelocation.code_length, cell, ih]; omega

theorem cell_match (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (fault : Nat) (tail : Code)
    (input : Tape) (bit : Bool) (left right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (cell fault bit) tail) oracle) 2
      (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier left (some bit :: right) }) =
      PMF.pure (CodeRelocation.frame 2
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (some bit :: left) right })) := by
  cases bit <;> cases right <;>
    simp [cell, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells, Tape.moveRight, CodeRelocation.frame, CodeRelocation.control,
      Machine.Configuration.rebasePc]

theorem match_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (fault : Nat) (tail : Code)
    (input : Tape) (bits : List Bool) (left right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (compareCode fault tail bits) oracle) (2 * bits.length)
      (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier left (bits.map some ++ right) }) =
      PMF.pure (CodeRelocation.frame (2 * bits.length)
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (bits.reverse.map some ++ left) right })) := by
  induction bits generalizing left with
  | nil => simp [compareCode, TimedExecution.eval, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc]
  | cons bit rest ih =>
      rw [show 2 * (bit :: rest).length = 2 + 2 * rest.length from by simp; omega, TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append, compareCode]
      rw [cell_match, PMF.pure_bind]
      have placed := CodeRelocation.eval (cell (fault + 2 * rest.length + 2) bit)
        (compareCode fault tail rest) oracle (2 * rest.length)
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (some bit :: left) (rest.map some ++ right) })
      rw [show (cell (fault + 2 * rest.length + 2) bit).length = 2 from rfl] at placed
      rw [placed, ih, PMF.pure_map]
      simp [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
        List.reverse_cons, List.map_append, List.append_assoc]

theorem mismatch_cell (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (fault : Nat) (tail : Code)
    (input : Tape) (bit actual : Bool) (left right : List (Option Bool)) (hne : actual ≠ bit) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (cell fault bit) tail) oracle) 1
      (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier left (some actual :: right) }) =
      PMF.pure (CodeRelocation.frame fault
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier left (some actual :: right) })) := by
  cases bit <;> cases actual <;>
    simp_all [cell, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.tape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

theorem mismatch_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (fault : Nat) (tail : Code) (input : Tape) :
    ∀ (expected actual : List Bool) (left right : List (Option Bool)),
      expected.length = actual.length → expected ≠ actual →
      ∃ k, k < actual.length ∧
        TimedExecution.eval (Reification.timedStep (compareCode fault tail expected) oracle) (2 * k + 1)
          (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier left (actual.map some ++ right) }) =
          PMF.pure (CodeRelocation.frame (2 * expected.length + fault)
            (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier ((actual.take k).reverse.map some ++ left) ((actual.drop k).map some ++ right) })) := by
  intro expected
  induction expected with
  | nil => intro actual left right hl hn; cases actual <;> simp_all
  | cons bit rest ih =>
      intro actual left right hl hn
      cases actual with
      | nil => simp at hl
      | cons cur actual =>
          by_cases hc : cur = bit
          · subst cur
            obtain ⟨k, hk, hr⟩ := ih actual (some bit :: left) right (by simpa using hl)
              (by intro he; exact hn (by rw [he]))
            refine ⟨k + 1, by simp; omega, ?_⟩
            rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) from by omega, TimedExecution.eval_add]
            simp only [compareCode, List.map_cons, List.cons_append]
            rw [cell_match, PMF.pure_bind]
            have placed := CodeRelocation.eval (cell (fault + 2 * rest.length + 2) bit)
              (compareCode fault tail rest) oracle (2 * k + 1)
              (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (some bit :: left) (actual.map some ++ right) })
            rw [show (cell (fault + 2 * rest.length + 2) bit).length = 2 from rfl] at placed
            rw [placed, hr, PMF.pure_map]
            simp [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
              List.take_succ_cons, List.drop_succ_cons, List.reverse_cons, List.map_append,
              List.append_assoc, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
          · refine ⟨0, by simp, ?_⟩
            simp only [compareCode, List.map_cons, List.cons_append]
            rw [mismatch_cell oracle state trace _ _ input bit cur left _ hc]
            simp [List.length_cons, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

theorem link (fault : Nat) (tail : Code) (bits : List Bool) :
    compareCode fault tail bits = CodeRelocation.host (compareCode fault [] bits) tail := by
  induction bits with
  | nil => simp [compareCode]
  | cons bit rest ih => rw [compareCode, ih, ← CodeRelocation.host_assoc]; rfl

def code (expected : List Bool) (accepted rejected : Code) : Code :=
  compareCode accepted.length (CodeRelocation.host accepted rejected) expected

def rejectedPrefix (expected : List Bool) (accepted : Code) : Code :=
  CodeRelocation.host (compareCode accepted.length [] expected) accepted

theorem rejected_host (expected : List Bool) (accepted rejected : Code) :
    code expected accepted rejected = CodeRelocation.host (rejectedPrefix expected accepted) rejected := by
  rw [code, link, ← CodeRelocation.host_assoc]; rfl

def recover (tail : Code) : Code :=
  CodeRelocation.host [.native (.moveLeft .output)] (LeftBlankRewind.code .output tail)

theorem recover_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (input : Tape)
    (past future : List Bool) (right : List (Option Bool)) (hne : future ≠ []) :
    TimedExecution.eval (Reification.timedStep (recover tail) oracle) (3 * past.length + 3)
      (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (past.reverse.map some ++ [none]) (future.map some ++ right) }) =
      PMF.pure (CodeRelocation.frame 5
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier [none] ((past ++ future).map some ++ right) })) := by
  have hm : (FixedWidthCopy.frontier (past.reverse.map some ++ [none]) (future.map some ++ right)).moveLeft =
      FixedWidthCopy.backwardFrontier (future.map some ++ right) (past.reverse.map some ++ [none]) := by
    cases future with
    | nil => contradiction
    | cons bit rest =>
        cases past.reverse <;> simp [FixedWidthCopy.frontier, ResponseLoading.fromCells,
          FixedWidthCopy.backwardFrontier, Tape.moveLeft]
  simp only [List.map_reverse] at hm
  have step : TimedExecution.eval (Reification.timedStep (recover tail) oracle) 1
      (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier (past.reverse.map some ++ [none]) (future.map some ++ right) }) =
      PMF.pure (CodeRelocation.frame 1
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.backwardFrontier (future.map some ++ right) (past.reverse.map some ++ [none]) })) := by
    simp [recover, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, NativeCode.frame, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
      hm, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  rw [show 3 * past.length + 3 = 1 + (3 * past.reverse.length + 2) from by simp; omega,
    TimedExecution.eval_add, step, PMF.pure_bind, recover]
  have placed := CodeRelocation.eval [.native (.moveLeft .output)] (LeftBlankRewind.code .output tail)
    oracle (3 * past.reverse.length + 2)
    (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.backwardFrontier (future.map some ++ right) (past.reverse.map some ++ [none]) })
  simp only [List.length_cons, List.length_nil] at placed
  rw [placed]
  have hr := LeftBlankRewind.run oracle state trace .output tail past.reverse (future.map some ++ right) [] input
  simp only [List.reverse_reverse, LeftBlankRewind.put] at hr
  rw [hr, PMF.pure_map]
  simp [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Machine.Configuration.rebasePc, List.map_append, List.append_assoc]

theorem rejected_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (expected actual : List Bool) (accepted rejected : Code)
    (input : Tape) (right : List (Option Bool)) (hl : expected.length = actual.length) (hn : expected ≠ actual) :
    ∃ k, k < actual.length ∧
      TimedExecution.eval (Reification.timedStep (code expected accepted (recover rejected)) oracle) (5 * k + 4)
        (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier [none] (actual.map some ++ right) }) =
        PMF.pure (CodeRelocation.frame ((rejectedPrefix expected accepted).length + 5)
          (NativeCode.frame state trace { inputTape := input, outputTape := FixedWidthCopy.frontier [none] (actual.map some ++ right) })) := by
  obtain ⟨k, hk, hr⟩ := mismatch_run oracle state trace accepted.length
    (CodeRelocation.host accepted (recover rejected)) input expected actual [none] right hl hn
  refine ⟨k, hk, ?_⟩
  have hlen : (rejectedPrefix expected accepted).length = 2 * expected.length + accepted.length := by
    simp [rejectedPrefix, CodeRelocation.code_length, compareCode_length]
  have hd : actual.drop k ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hh
    omega
  have hre := recover_run oracle state trace rejected input (actual.take k) (actual.drop k) right hd
  have htake : (actual.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk.le]
  rw [htake, List.take_append_drop] at hre
  rw [show 5 * k + 4 = (2 * k + 1) + (3 * k + 3) from by omega, TimedExecution.eval_add]
  change (TimedExecution.eval (Reification.timedStep (compareCode _ _ _) oracle) _ _).bind _ = _
  rw [hr, PMF.pure_bind]
  rw [← hlen]
  rw [rejected_host, CodeRelocation.eval, hre, PMF.pure_map]
  simp [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc]

theorem code_native (expected : List Bool) (accepted rejected : Code)
    (ha : ∀ op ∈ accepted, ∃ native, op = .native native)
    (hr : ∀ op ∈ rejected, ∃ native, op = .native native) :
    ∀ op ∈ code expected accepted rejected, ∃ native, op = .native native := by
  have native (fault : Nat) (tail : Code) (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
      ∀ bits, ∀ op ∈ compareCode fault tail bits, ∃ native, op = .native native := by
    intro bits
    induction bits with
    | nil => exact ht
    | cons bit rest ih =>
        apply CodeRelocation.host_native _ _ _ ih
        intro op hm
        simp only [cell, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> exact ⟨_, rfl⟩
  exact native _ _ (CodeRelocation.host_native _ _ ha hr) _

end CryptoOracle.Interactive.ForwardConstantCheck
