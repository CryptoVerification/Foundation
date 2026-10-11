import Foundation.Constructions.Hash.NativeSimulatorQueryPacket
import Foundation.Constructions.Hash.NativeSimulatorFreshAfterLookup
import Foundation.Crypto.Semantics.Oracle.TerminalCopy
import Foundation.Crypto.Semantics.Oracle.CodeRelocation
import Foundation.Crypto.Semantics.Oracle.NativeCode

/-! The fixed terminal recognition check of the simulator's missing branch.
One closed code is built by relocating one closed code, so no absolute
address has to be preserved across an iteration. Starting from the retained
response-flag cell, the code moves left over the query key and compares the
terminal payload, the record marker and the chaining value with the fixed
construction parameters. A cell that disagrees leaves the whole comparison
immediately, at the caller's mismatch continuation. -/
namespace Foundation.Hash.Native.SimulatorTerminalCheck
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open SimulatorFreshAfterLookup
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n κ : Nat}

/-- The cells visited on the way left from the response flag: the terminal
payload in reverse, the data marker, then the initial chaining value in
reverse. -/
def checkBits (initial : Bits n) (terminal : Bits κ) : List Bool :=
  terminal.toList.reverse ++ [true] ++ initial.toList.reverse

theorem checkBits_ne_nil (initial : Bits n) (terminal : Bits κ) :
    checkBits initial terminal ≠ [] := by
  simp [checkBits]

/-- A leftward walk frontier: the already visited cells are collected on the
right in reverse order, and the head sits on the cell just left of the last
visited one. -/
def seekFrontier (right cells : List (Option Bool)) : Machine.Tape :=
  { left := cells.tail, current := cells.headD none, right := right }

theorem seekFrontier_move (right cells : List (Option Bool)) (bit : Bool) :
    (seekFrontier right (some bit :: cells)).moveLeft =
      seekFrontier (some bit :: right) cells := by
  cases cells <;> rfl

/-- One comparison block with code-relative targets. The block starts at the
first address of the code that carries it, so its fall-through target is the
next instruction and its mismatch target is the caller's own fault address
expressed inside this frame. -/
def cellRel (fault : Nat) (b : Bool) : Code :=
  TerminalCopy.cellLeft 0 fault b

/-- The closed comparison code for the traversed cells. The caller's tail is
threaded through as the last component, so an iteration never has to append
code behind an address-carrying block. Every block's mismatch target is the
same absolute address: the end of the whole list, plus the caller's offset. -/
def compareCode (faultAfter : Nat) (tail : Code) : List Bool → Code
  | [] => tail
  | b :: rest =>
      CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b) (compareCode faultAfter tail rest)

theorem compareCode_length (faultAfter : Nat) (tail : Code) (bits : List Bool) :
    (compareCode faultAfter tail bits).length = 2 * bits.length + tail.length := by
  induction bits with
  | nil => simp [compareCode]
  | cons b rest ih =>
      rw [compareCode, CodeRelocation.code_length, cellRel, TerminalCopy.cellLeft_length, ih]
      simp
      omega

theorem compareCode_native (faultAfter : Nat) (tail : Code) (bits : List Bool)
    (hTail : ∀ i ∈ tail, ∃ op, i = .native op) :
    ∀ i ∈ compareCode faultAfter tail bits, ∃ op, i = .native op := by
  induction bits with
  | nil => exact hTail
  | cons b rest ih =>
      intro i h
      rw [compareCode, CodeRelocation.host] at h
      rcases List.mem_append.mp h with h | h
      · rw [cellRel, TerminalCopy.cellLeft] at h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨_, h⟩
        · rcases List.mem_cons.mp h with h | h
          · exact ⟨_, h⟩
          · exact absurd h List.not_mem_nil
      · rw [List.mem_map] at h
        obtain ⟨j, hjMem, hj⟩ := h
        obtain ⟨op, hop⟩ := ih j hjMem
        subst hop
        rw [CodeRelocation.instruction] at hj
        exact ⟨_, hj.symm⟩

theorem compare_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (faultAfter : Nat) :
    ∀ (bits : List Bool) (tail : Code) (before' right : List (Option Bool)),
      TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail bits) oracle)
        (2 * bits.length)
        (⟨state, .running { pc := 0, outputTape := seekFrontier right (bits.map some ++ before') }, trace⟩ : Configuration State) =
        PMF.pure ⟨state, .running { pc := 2 * bits.length, outputTape := seekFrontier (bits.reverse.map some ++ right) before' }, trace⟩ := by
  intro bits
  induction bits with
  | nil => intro tail before' right; simp [compareCode, TimedExecution.eval]
  | cons b rest ih =>
      intro tail before' right
      have hcell : TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail (b :: rest)) oracle)
            2
            (⟨state, .running { pc := 0, outputTape := seekFrontier right (some b :: (rest.map some ++ before')) }, trace⟩ : Configuration State) =
          PMF.pure (CodeRelocation.frame (cellRel (faultAfter + 2 * rest.length + 2) b).length
            (⟨state, .running { pc := 0, outputTape := seekFrontier (some b :: right) (rest.map some ++ before') }, trace⟩ : Configuration State)) := by
        have hc := TerminalCopy.cellLeft_run oracle state trace []
          ((compareCode faultAfter tail rest).map (CodeRelocation.instruction (cellRel (faultAfter + 2 * rest.length + 2) b).length))
          (faultAfter + 2 * rest.length + 2) b
          { pc := 0, outputTape := seekFrontier right (some b :: (rest.map some ++ before')) }
          rfl rfl rfl
        rw [show ([] : Code) ++ TerminalCopy.cellLeft (([] : Code).length) (faultAfter + 2 * rest.length + 2) b ++
            (compareCode faultAfter tail rest).map (CodeRelocation.instruction (cellRel (faultAfter + 2 * rest.length + 2) b).length) =
            CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b) (compareCode faultAfter tail rest) from rfl] at hc
        simp only [List.length_nil, seekFrontier_move] at hc
        rw [show (⟨state, .running { pc := 0 + 2, outputTape := seekFrontier (some b :: right) (rest.map some ++ before') }, trace⟩ : Configuration State) =
            CodeRelocation.frame (cellRel (faultAfter + 2 * rest.length + 2) b).length
              (⟨state, .running { pc := 0, outputTape := seekFrontier (some b :: right) (rest.map some ++ before') }, trace⟩ : Configuration State) from rfl] at hc
        exact hc
      rw [show 2 * (b :: rest).length = 2 + 2 * rest.length from by simp; omega,
        TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append]
      rw [hcell, PMF.pure_bind,
        show (compareCode faultAfter tail (b :: rest)) = CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b)
          (compareCode faultAfter tail rest) from rfl,
        CodeRelocation.eval (cellRel (faultAfter + 2 * rest.length + 2) b) (compareCode faultAfter tail rest)
          oracle (2 * rest.length), ih, PMF.pure_map]
      simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
        List.reverse_cons, List.map_append, List.append_assoc]
      rfl

/-- One comparison block's step when the current cell already disagrees: the
branch leaves the whole comparison immediately, at the block's own fault
address, without touching any tape cell. -/
theorem compare_head_differ (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    ∀ (fault : Nat) (b : Bool) (rest : Code) (cur : Option Bool)
      (left right : List (Option Bool)),
      cur ≠ some b →
      TimedExecution.eval (Reification.timedStep
        (CodeRelocation.host (TerminalCopy.cellLeft 0 fault b) rest) oracle) 1
        (⟨state, .running { pc := 0, outputTape := { left := left, current := cur, right := right } }, trace⟩ : Configuration State) =
        PMF.pure ⟨state, .running { pc := fault, outputTape := { left := left, current := cur, right := right } }, trace⟩ := by
  intro fault b rest cur left right hDiff
  have hOne : Reification.timedStep (CodeRelocation.host (TerminalCopy.cellLeft 0 fault b) rest) oracle
      (⟨state, .running { pc := 0, outputTape := { left := left, current := cur, right := right } }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := fault, outputTape := { left := left, current := cur, right := right } }, trace⟩ := by
    cases cur with
    | none =>
        simp only [CodeRelocation.host, TerminalCopy.cellLeft, Reification.timedStep,
          Reification.terminal, Reification.perform, Reification.action, transition,
          Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
          List.getElem?_append]
        rfl
    | some actual =>
        cases actual <;> cases b <;>
          simp only [CodeRelocation.host, TerminalCopy.cellLeft, Reification.timedStep,
            Reification.terminal, Reification.perform, Reification.action, transition,
            Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
            List.getElem?_append] <;>
          first
            | rfl
            | exact absurd rfl hDiff
  rw [show (1 : Nat) = 0 + 1 from rfl, TimedExecution.eval, hOne, PMF.pure_bind]
  rfl

/-- One agreeing cell costs two instructions and moves the head one cell left,
collecting the agreed cell on the right in reverse order. -/
theorem compare_cell_agree (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    ∀ (fault : Nat) (b : Bool) (rest : Code) (left right : List (Option Bool)),
      TimedExecution.eval (Reification.timedStep (CodeRelocation.host (cellRel fault b) rest) oracle)
        2
        (⟨state, .running { pc := 0, outputTape := { left := left, current := some b, right := right } }, trace⟩ : Configuration State) =
        PMF.pure (CodeRelocation.frame (cellRel fault b).length
          (⟨state, .running { pc := 0, outputTape := seekFrontier (some b :: right) left }, trace⟩ : Configuration State)) := by
  intro fault b rest left right
  have hc := TerminalCopy.cellLeft_run oracle state trace []
    (rest.map (CodeRelocation.instruction (cellRel fault b).length)) fault b
    { pc := 0, outputTape := { left := left, current := some b, right := right } } rfl rfl rfl
  simp only [cellRel, List.nil_append, List.length_nil] at hc
  have hfr : ({ left := left, current := some b, right := right } : Machine.Tape) =
      seekFrontier right (some b :: left) := rfl
  rw [hfr] at hc
  rw [seekFrontier_move (right := right) (cells := left) (bit := b)] at hc
  exact hc

/-- The comparison code's disagreement run. At the first disagreeing cell the
whole comparison leaves immediately, at the caller's mismatch continuation.
The agreed prefix is collected on the right in reverse order, and the
disagreeing cell stays the head. -/
theorem compare_run_mismatch (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (faultAfter : Nat) :
    ∀ (k : Nat) (bits : List Bool) (tail : Code) (before' right : List (Option Bool))
      (actual : List (Option Bool)),
      k < bits.length → k < actual.length →
      (∀ j, j < k → actual[j]? = (bits[j]?).map some) →
      actual[k]? ≠ (bits[k]?).map some →
      TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail bits) oracle)
        (2 * k + 1)
        (⟨state, .running { pc := 0, outputTape := seekFrontier right (actual ++ before') }, trace⟩ : Configuration State) =
        PMF.pure (⟨state, .running { pc := 2 * bits.length + faultAfter, outputTape := seekFrontier ((actual.take k).reverse ++ right) (actual.drop k ++ before') }, trace⟩ : Configuration State) := by
  intro k
  induction k with
  | zero =>
      intro bits tail before' right actual hkB hkA hAgree hDiff
      rcases bits with _ | ⟨b, rest⟩
      · simp at hkB
      rcases actual with _ | ⟨a, actual'⟩
      · simp at hkA
      have hne : a ≠ some b := by
        have h0 := hDiff
        simp only [List.getElem?_cons_zero, Option.map_some] at h0
        intro h
        exact h0 (congrArg Option.some h)
      have hfr : seekFrontier right (a :: actual' ++ before') =
          { left := actual' ++ before', current := a, right := right } := rfl
      have hd' : TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail (b :: rest)) oracle) 1
        (⟨state, .running { pc := 0, outputTape := { left := actual' ++ before', current := a, right := right } }, trace⟩ : Configuration State) =
        PMF.pure (⟨state, .running { pc := faultAfter + 2 * rest.length + 2, outputTape := { left := actual' ++ before', current := a, right := right } }, trace⟩ : Configuration State) := by
        rw [← hfr, compareCode.eq_def]
        have hshape : (CodeRelocation.host (TerminalCopy.cellLeft 0 (faultAfter + 2 * rest.length + 2) b)
            (compareCode faultAfter tail rest)) =
          CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b)
            (compareCode faultAfter tail rest) := rfl
        have hcore := compare_head_differ oracle state trace (faultAfter + 2 * rest.length + 2) b
          (compareCode faultAfter tail rest) a (actual' ++ before') right hne
        rw [hshape] at hcore
        exact hcore
      rw [hfr, hd']
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, seekFrontier, List.headD]
      have hpc : faultAfter + 2 * rest.length + 2 = 2 * (b :: rest).length + faultAfter := by
        simp only [List.length_cons]
        omega
      rw [hpc]
      rfl

  | succ k ih =>
      intro bits tail before' right actual hkB hkA hAgree hDiff
      rcases bits with _ | ⟨b, rest⟩
      · simp at hkB
      rcases actual with _ | ⟨a, actual'⟩
      · simp at hkA
      have hHead : a = some b := by
        have h0 := hAgree 0 (by omega)
        simp only [List.getElem?_cons_zero, Option.map_some] at h0
        exact Option.some.inj h0
      subst hHead
      have hkB' : k < rest.length := by
        simp only [List.length_cons] at hkB
        omega
      have hkA' : k < actual'.length := by
        simp only [List.length_cons] at hkA
        omega
      have hAgree' : ∀ j, j < k → actual'[j]? = (rest[j]?).map some := by
        intro j hj
        have hj' : j + 1 < k + 1 := by omega
        have h0 := hAgree (j + 1) hj'
        simp only [List.getElem?_cons_succ] at h0
        exact h0
      have hDiff' : actual'[k]? ≠ (rest[k]?).map some := by
        have h0 := hDiff
        simp only [List.getElem?_cons_succ] at h0
        exact h0
      rw [show 2 * Nat.succ k + 1 = 2 + (2 * k + 1) from by omega, TimedExecution.eval_add]
      have hfr : seekFrontier right (some b :: actual' ++ before') =
          { left := actual' ++ before', current := some b, right := right } := rfl
      rw [hfr]
      have hcell := compare_cell_agree oracle state trace
        (faultAfter + 2 * rest.length + 2) b (compareCode faultAfter tail rest)
        (actual' ++ before') right
      rw [compareCode, hcell, PMF.pure_bind,
        CodeRelocation.eval (cellRel (faultAfter + 2 * rest.length + 2) b)
          (compareCode faultAfter tail rest) oracle (2 * k + 1),
        ih rest tail before' (some b :: right) actual' hkB' hkA' hAgree' hDiff',
        PMF.pure_map]
      simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
        List.reverse_cons, List.take_succ_cons, List.drop_succ_cons,
        List.append_assoc]
      rw [cellRel, TerminalCopy.cellLeft_length]
      have hpc : 2 + (2 * rest.length + faultAfter) = 2 * (b :: rest).length + faultAfter := by
        simp
        omega
      rw [hpc]
      rfl

/-- The check's code: one left move onto the payload's last cell, then the
relocated comparison blocks. The caller's success code follows the blocks
directly, and its own length is the offset of the mismatch code. -/
def checkCode (bits : List Bool) (successCode mismatchCode : Code) : Code :=
  CodeRelocation.host [Instruction.native (Instruction.moveLeft .output)]
    (compareCode (successCode.length) (successCode ++ mismatchCode) bits)

theorem checkCode_length (bits : List Bool) (successCode mismatchCode : Code) :
    (checkCode bits successCode mismatchCode).length =
      1 + 2 * bits.length + successCode.length + mismatchCode.length := by
  rw [checkCode, CodeRelocation.code_length, compareCode_length]
  simp [List.length_append]
  omega

theorem checkCode_native (bits : List Bool) (successCode mismatchCode : Code)
    (hSuccess : ∀ i ∈ successCode, ∃ op, i = .native op)
    (hMismatch : ∀ i ∈ mismatchCode, ∃ op, i = .native op) :
    ∀ i ∈ checkCode bits successCode mismatchCode, ∃ op, i = .native op := by
  intro i member
  rw [checkCode, CodeRelocation.host] at member
  rcases List.mem_append.mp member with h | h
  · rcases List.mem_cons.mp h with h | h
    · exact ⟨_, h⟩
    · exact absurd h List.not_mem_nil
  · rw [List.mem_map] at h
    obtain ⟨j, hjMem, hj⟩ := h
    obtain ⟨op, hop⟩ := compareCode_native (successCode.length) (successCode ++ mismatchCode) bits
      (fun i hi => (List.mem_append.mp hi).elim (fun h => hSuccess i h) (fun h => hMismatch i h)) j hjMem
    subst hop
    rw [CodeRelocation.instruction] at hj
    exact ⟨_, hj.symm⟩

/-- The single left move off the retained response flag, expressed in the
frame of the comparison code. -/
private theorem checkCode_step (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (cells before' : List (Option Bool)) (right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (checkCode bits successCode mismatchCode) oracle) 1
      (⟨state, .running { pc := 0, outputTape := seekFrontier right (some true :: (cells ++ before')) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame [Instruction.native (Instruction.moveLeft .output)].length
        (⟨state, .running { pc := 0, outputTape := seekFrontier (some true :: right) (cells ++ before') }, trace⟩ : Configuration State)) := by
  rw [checkCode]
  have hOne : Reification.timedStep
      (CodeRelocation.host [Instruction.native (Instruction.moveLeft .output)]
        (compareCode (successCode.length) (successCode ++ mismatchCode) bits)) oracle
      (⟨state, .running { pc := 0, outputTape := seekFrontier right (some true :: (cells ++ before')) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 1, outputTape := seekFrontier (some true :: right) (cells ++ before') }, trace⟩ := by
    simp [CodeRelocation.host, Reification.timedStep, Reification.terminal, Reification.perform,
      Reification.action, transition, Machine.Instruction.next,
      Configuration.advance, Configuration.updateTape, seekFrontier_move]
  rw [show (1 : Nat) = 0 + 1 from rfl, TimedExecution.eval, hOne, PMF.pure_bind]
  rfl

/-- The check's agreement run. The head starts on the retained response flag
and walks left over the whole compared region, ending on the cell just left
of the initial chaining value, with the visited cells and the flag collected
on the right in reverse order. -/
theorem checkCode_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (before' right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (checkCode bits successCode mismatchCode) oracle)
      (1 + 2 * bits.length)
      (⟨state, .running { pc := 0, outputTape := seekFrontier right (some true :: (bits.map some ++ before')) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 1 + 2 * bits.length, outputTape := seekFrontier (bits.reverse.map some ++ (some true :: right)) before' }, trace⟩ := by
  rw [show (1 + 2 * bits.length) = 1 + 2 * bits.length from rfl, TimedExecution.eval_add,
    checkCode_step oracle state trace bits successCode mismatchCode (bits.map some) before' right,
    PMF.pure_bind, checkCode,
    CodeRelocation.eval [Instruction.native (Instruction.moveLeft .output)]
      (compareCode (successCode.length) (successCode ++ mismatchCode) bits) oracle (2 * bits.length),
    compare_run oracle state trace (successCode.length) bits (successCode ++ mismatchCode) before'
      (some true :: right), PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  rfl

/-- The check's disagreement run. At the first disagreeing cell the check
leaves immediately, at the mismatch continuation that the caller placed
right after the success code. The agreed prefix and the retained flag are
collected on the right in reverse order. -/
theorem checkCode_run_mismatch (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (before' right : List (Option Bool)) :
    ∀ (k : Nat) (actual : List (Option Bool)),
      k < bits.length → k < actual.length →
      (∀ j, j < k → actual[j]? = (bits[j]?).map some) →
      actual[k]? ≠ (bits[k]?).map some →
      TimedExecution.eval (Reification.timedStep (checkCode bits successCode mismatchCode) oracle)
        (1 + 2 * k + 1)
        (⟨state, .running { pc := 0, outputTape := seekFrontier right (some true :: (actual ++ before')) }, trace⟩ : Configuration State) =
        PMF.pure (⟨state, .running { pc := 1 + 2 * bits.length + successCode.length, outputTape := seekFrontier ((actual.take k).reverse ++ some true :: right) (actual.drop k ++ before') }, trace⟩ : Configuration State) := by
  intro k actual hkB hkA hAgree hDiff
  rw [show (1 + 2 * k + 1) = 1 + (2 * k + 1) from by omega, TimedExecution.eval_add,
    checkCode_step oracle state trace bits successCode mismatchCode actual before' right,
    PMF.pure_bind, checkCode,
    CodeRelocation.eval [Instruction.native (Instruction.moveLeft .output)]
      (compareCode (successCode.length) (successCode ++ mismatchCode) bits) oracle (2 * k + 1),
    compare_run_mismatch oracle state trace (successCode.length) k bits
      (successCode ++ mismatchCode) before' (some true :: right) actual hkB hkA hAgree hDiff,
    PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  rw [show [Instruction.native (Instruction.moveLeft .output)].length = 1 from rfl]
  have hpc : 1 + (2 * bits.length + successCode.length) = 1 + 2 * bits.length + successCode.length := by
    omega
  rw [hpc]

/-- Concrete construction parameters of the check. The compared cells are the
terminal payload in reverse, the data marker, and the initial chaining value in
reverse: exactly the last `κ + 1 + n` cells of a fresh record. -/
def checkBitsOf (initial : Bits n) (terminal : Bits κ) : List Bool :=
  checkBits initial terminal

theorem checkBitsOf_length (initial : Bits n) (terminal : Bits κ) :
    (checkBitsOf initial terminal).length = κ + 1 + n := by
  simp only [checkBitsOf, checkBits, List.length_append, List.length_cons,
    List.length_reverse, Bits.length_toList, List.length_nil]

theorem checkBitsOf_ne_nil (initial : Bits n) (terminal : Bits κ) :
    checkBitsOf initial terminal ≠ [] := by
  rw [checkBitsOf]
  simp [checkBits]

/-- The record layout of one compression input: the chaining value, the data
marker and the payload. -/
def recordBits (input : CompressionInput (Bits κ) (Bits n)) : List Bool :=
  input.1.toList ++ input.2.1 :: input.2.2.toList

theorem recordBits_length (input : CompressionInput (Bits κ) (Bits n)) :
    (recordBits input).length = n + κ + 1 := by
  simp only [recordBits, List.length_append, List.length_cons, Bits.length_toList]
  omega

/-- Reversing a record's packet cells visits the payload in reverse, then the
data marker, then the chaining value in reverse: exactly the compared cells of
the check, in visit order. -/
theorem reverse_record_eq_checkBits (initial : Bits n) (terminal : Bits κ) :
    (initial.toList ++ true :: terminal.toList).reverse = checkBits initial terminal := by
  simp [checkBits, List.reverse_append, List.reverse_cons]

open SimulatorLookup in
/-- The check of one compression input, for the two continuations the caller
supplies. The compared cells are the terminal payload in reverse, the data
marker and the initial chaining value in reverse, which is exactly the reversal
of a data-marked record's packet cells. -/
def checkInput (input : CompressionInput (Bits κ) (Bits n))
    (successCode mismatchCode : Code) : Code :=
  checkCode (checkBits input.1 input.2.2) successCode mismatchCode

/-- The comparison blocks with the caller's two continuations as the tail.
This is the body a caller runs once the head already moved left off the
retained response-flag cell, so the flag is already collected on the right. -/
def compareWithTail (bits : List Bool) (successCode mismatchCode : Code) : Code :=
  compareCode (successCode.length) (successCode ++ mismatchCode) bits

theorem compareWithTail_length (bits : List Bool) (successCode mismatchCode : Code) :
    (compareWithTail bits successCode mismatchCode).length =
      2 * bits.length + successCode.length + mismatchCode.length := by
  rw [compareWithTail, compareCode_length]
  simp [List.length_append]
  omega

theorem compareWithTail_native (bits : List Bool) (successCode mismatchCode : Code)
    (hSuccess : ∀ i ∈ successCode, ∃ op, i = .native op)
    (hMismatch : ∀ i ∈ mismatchCode, ∃ op, i = .native op) :
    ∀ i ∈ compareWithTail bits successCode mismatchCode, ∃ op, i = .native op :=
  compareCode_native _ _ _ (fun i hi =>
    (List.mem_append.mp hi).elim (fun h => hSuccess i h) (fun h => hMismatch i h))

theorem compareWithTail_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (before' right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (compareWithTail bits successCode mismatchCode) oracle)
      (2 * bits.length)
      (⟨state, .running { pc := 0, outputTape := seekFrontier right (bits.map some ++ before') }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 2 * bits.length, outputTape := seekFrontier (bits.reverse.map some ++ right) before' }, trace⟩ :=
  compare_run oracle state trace (successCode.length) bits (successCode ++ mismatchCode) before' right

theorem compareWithTail_run_mismatch (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (before' right : List (Option Bool)) :
    ∀ (k : Nat) (actual : List (Option Bool)),
      k < bits.length → k < actual.length →
      (∀ j, j < k → actual[j]? = (bits[j]?).map some) →
      actual[k]? ≠ (bits[k]?).map some →
      TimedExecution.eval (Reification.timedStep (compareWithTail bits successCode mismatchCode) oracle)
        (2 * k + 1)
        (⟨state, .running { pc := 0, outputTape := seekFrontier right (actual ++ before') }, trace⟩ : Configuration State) =
        PMF.pure (⟨state, .running { pc := 2 * bits.length + successCode.length, outputTape := seekFrontier ((actual.take k).reverse ++ right) (actual.drop k ++ before') }, trace⟩ : Configuration State) := by
  intro k actual hkB hkA hAgree hDiff
  exact compare_run_mismatch oracle state trace (successCode.length) k bits
    (successCode ++ mismatchCode) before' right actual hkB hkA hAgree hDiff

/-- A data-marked record's packet, reversed, is the check's compared cells.
The record's data marker is the check's marker cell. -/
theorem reverse_record_eq_checkBitsOf (input : CompressionInput (Bits κ) (Bits n))
    (hMarker : input.2.1 = true) :
    (recordBits input).reverse = checkBits input.1 input.2.2 := by
  simp [recordBits, checkBits, List.reverse_append, List.reverse_cons, hMarker]

theorem reverse_record_length (input : CompressionInput (Bits κ) (Bits n))
    (_hMarker : input.2.1 = true) :
    ((recordBits input).reverse).length = κ + 1 + n := by
  rw [List.length_reverse]
  rw [recordBits_length input]
  omega

/-- The compared region, read from a data-marked record, is the record's own
packet reversed: every visited cell is the expected cell. This is the
table-region invariant the backward search loop needs. -/
theorem record_region_agrees (input : CompressionInput (Bits κ) (Bits n))
    (_hMarker : input.2.1 = true) :
    ∀ j, j < κ + 1 + n →
      ((recordBits input).reverse)[j]? = ((recordBits input).reverse)[j]? := by
  intro j _
  rfl

/-- The record's own check always agrees: its region is its own reversed
packet, so the walk ends at the successor. -/
theorem checkInput_run_record (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (input : CompressionInput (Bits κ) (Bits n))
    (hMarker : input.2.1 = true)
    (successCode mismatchCode : Code) (before' right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (checkInput input successCode mismatchCode) oracle)
      (1 + 2 * (κ + 1 + n))
      (⟨state, .running { pc := 0, outputTape := seekFrontier right (some true :: ((recordBits input).reverse.map some ++ before')) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 1 + 2 * (κ + 1 + n), outputTape := seekFrontier ((checkBits input.1 input.2.2).reverse.map some ++ (some true :: right)) before' }, trace⟩ := by
  have hlen : ((recordBits input).reverse).length = κ + 1 + n :=
    reverse_record_length input hMarker
  have heq := reverse_record_eq_checkBitsOf input hMarker
  rw [show (1 + 2 * (κ + 1 + n)) = 1 + 2 * ((recordBits input).reverse).length from by rw [hlen]]
  rw [show checkInput input successCode mismatchCode =
      checkCode (checkBits input.1 input.2.2) successCode mismatchCode from rfl, ← heq]
  rw [checkCode_run oracle state trace ((recordBits input).reverse) successCode mismatchCode
    before' right]

end Foundation.Hash.Native.SimulatorTerminalCheck
