import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy
import Foundation.Crypto.Semantics.Oracle.CodeRelocation

/-! Read a fixed field leftwards and prepend it on the output tape. In escaped
mode, read every second cell to decode the existing true/bit representation.
The output's old left cells are explicitly scratch space; its saved right suffix
and the entire input table are retained. Every allocation is a real head move. -/
namespace CryptoOracle.Interactive.BackwardFieldCopy
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def writeLeft : List (Option Bool) → Tape → Tape
  | [], tape => tape
  | cell :: rest, tape => writeLeft rest ((tape.write cell).moveLeft)

theorem writeLeft_append (first second : List (Option Bool)) (tape : Tape) :
    writeLeft (first ++ second) tape = writeLeft second (writeLeft first tape) := by
  induction first generalizing tape with
  | nil => rfl
  | cons cell rest ih => exact ih _

/-- A sufficiently long prepend overwrites all obsolete target cells and then
grows into fresh blank cells on the left. The right suffix is never overwritten. -/
theorem writeLeft_finish (cells left right : List (Option Bool)) (current : Option Bool)
    (longer : left.length < cells.length) :
    writeLeft cells { left := left, current := current, right := right } =
      { current := none, right := cells.reverse ++ right } := by
  induction cells generalizing left current right with
  | nil => simp at longer
  | cons cell rest ih =>
      cases left with
      | nil =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              rw [writeLeft]
              have h := ih [] (cell :: right) none (by simp)
              simpa only [Tape.write, Tape.moveLeft, List.reverse_cons, List.append_assoc,
                List.singleton_append, List.cons_append, List.nil_append] using h
      | cons old left =>
          have hl : left.length < rest.length := by simpa using longer
          rw [writeLeft]
          have h := ih left (cell :: right) old hl
          simpa only [Tape.write, Tape.moveLeft, List.reverse_cons, List.append_assoc,
            List.singleton_append] using h

def stride (escaped : Bool) : Nat := if escaped then 2 else 1
def cellWidth (escaped : Bool) : Nat := 6 + stride escaped
def cellSteps (escaped : Bool) : Nat := 4 + stride escaped

def chunk (escaped : Bool) (bit : Bool) : List (Option Bool) :=
  if escaped then [some bit, some true] else [some bit]

def sourceCells (escaped : Bool) (bits : List Bool) : List (Option Bool) :=
  bits.flatMap (chunk escaped)

theorem sourceCells_cons (escaped : Bool) (bit : Bool) (rest : List Bool) :
    sourceCells escaped (bit :: rest) = chunk escaped bit ++ sourceCells escaped rest := rfl

def cellCode (escaped : Bool) (base fault : Nat) : Code :=
  [.native (.branch .input fault (base + 1) (base + 3)),
   .native (.write .output false), .native (.jump (base + 5)),
   .native (.write .output true), .native (.jump (base + 5))] ++
  List.replicate (stride escaped) (.native (.moveLeft .input)) ++ [.native (.moveLeft .output)]

def code (escaped : Bool) (base : Nat) : Nat → Nat → Code
  | 0, _ => []
  | width + 1, fault => cellCode escaped base fault ++ code escaped (base + cellWidth escaped) width fault

theorem cellCode_length (escaped : Bool) (base fault : Nat) :
    (cellCode escaped base fault).length = cellWidth escaped := by
  simp [cellCode, cellWidth]
  omega

theorem code_length (escaped : Bool) (base width fault : Nat) :
    (code escaped base width fault).length = cellWidth escaped * width := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih => simp [code, cellCode_length, ih, Nat.mul_add, Nat.add_comm]

theorem cellCode_native (escaped : Bool) (base fault : Nat) :
    ∀ op ∈ cellCode escaped base fault, ∃ native, op = .native native := by
  intro op hm
  simp only [cellCode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hm
  rcases hm with ((rfl | rfl | rfl | rfl | rfl) | ⟨_, rfl⟩) | rfl <;> exact ⟨_, rfl⟩

theorem code_native (escaped : Bool) (base width fault : Nat) :
    ∀ op ∈ code escaped base width fault, ∃ native, op = .native native := by
  induction width generalizing base with
  | zero => simp [code]
  | succ width ih =>
      intro op hm
      rcases List.mem_append.mp hm with hm | hm
      · exact cellCode_native escaped base fault op hm
      · exact ih _ op hm

theorem cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (escaped : Bool) (fault : Nat)
    (sourceRight sourceLeft : List (Option Bool)) (target : Tape) (bit : Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ cellCode escaped before.length fault ++ after) oracle)
      (cellSteps escaped)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.backwardFrontier sourceRight (chunk escaped bit ++ sourceLeft), outputTape := target }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + cellWidth escaped, inputTape := FixedWidthCopy.backwardFrontier ((chunk escaped bit).reverse ++ sourceRight) sourceLeft, outputTape := (target.write (some bit)).moveLeft }, trace⟩ := by
  cases escaped <;> cases bit <;> cases sourceLeft <;>
    simp [cellCode, stride, cellWidth, cellSteps, chunk, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, FixedWidthCopy.backwardFrontier, Tape.moveLeft,
      List.getElem?_append, Nat.add_assoc]

/-- Decoding is performed by the real stride-two input movements. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (escaped : Bool) (fault : Nat)
    (sourceRight sourceLeft : List (Option Bool)) (target : Tape) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ code escaped before.length bits.length fault ++ after) oracle)
      (cellSteps escaped * bits.length)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.backwardFrontier sourceRight (sourceCells escaped bits ++ sourceLeft), outputTape := target }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + cellWidth escaped * bits.length, inputTape := FixedWidthCopy.backwardFrontier ((sourceCells escaped bits).reverse ++ sourceRight) sourceLeft, outputTape := writeLeft (bits.map some) target }, trace⟩ := by
  induction bits generalizing before sourceRight target with
  | nil => simp [sourceCells, code, TimedExecution.eval, writeLeft]
  | cons bit rest ih =>
      rw [show cellSteps escaped * (bit :: rest).length = cellSteps escaped + cellSteps escaped * rest.length from by simp [Nat.mul_add, Nat.add_comm],
        TimedExecution.eval_add]
      have hcell := cell_run oracle state trace before
        (code escaped (before.length + cellWidth escaped) rest.length fault ++ after) escaped fault
        sourceRight (sourceCells escaped rest ++ sourceLeft) target bit
      simp only [List.length_cons, code, sourceCells_cons, List.append_assoc] at ⊢
      simp only [List.append_assoc] at hcell
      rw [hcell, PMF.pure_bind]
      have hrest := ih (before ++ cellCode escaped before.length fault)
        ((chunk escaped bit).reverse ++ sourceRight) ((target.write (some bit)).moveLeft)
      simp only [List.length_append, cellCode_length, List.append_assoc] at hrest
      rw [hrest]
      simp [sourceCells, List.reverse_append, List.append_assoc, List.map_cons, writeLeft,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem raw_sourceCells (bits : List Bool) : sourceCells false bits = bits.map some := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [sourceCells_cons, chunk, ih]

/-- The fixed-field copier falls through into an actually relocated continuation. -/
theorem run_host (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (escaped : Bool)
    (sourceRight sourceLeft : List (Option Bool)) (target : Tape) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (code escaped 0 bits.length 0) tail) oracle)
      (cellSteps escaped * bits.length)
      (⟨state, .running { inputTape := FixedWidthCopy.backwardFrontier sourceRight (sourceCells escaped bits ++ sourceLeft), outputTape := target }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (code escaped 0 bits.length 0).length
        (⟨state, .running { inputTape := FixedWidthCopy.backwardFrontier ((sourceCells escaped bits).reverse ++ sourceRight) sourceLeft, outputTape := writeLeft (bits.map some) target }, trace⟩ : Configuration State)) := by
  have h := run oracle state trace [] (tail.map (CodeRelocation.instruction (code escaped 0 bits.length 0).length))
    escaped 0 sourceRight sourceLeft target bits
  simpa only [CodeRelocation.host, List.nil_append, List.length_nil, Nat.zero_add,
    CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc, code_length, Nat.add_zero] using h

theorem sourceCells_append (escaped : Bool) (first second : List Bool) :
    sourceCells escaped (first ++ second) = sourceCells escaped first ++ sourceCells escaped second := by
  simp [sourceCells]

theorem backward_move (right cells : List (Option Bool)) (cell : Option Bool) :
    (FixedWidthCopy.backwardFrontier right (cell :: cells)).moveLeft =
      FixedWidthCopy.backwardFrontier (cell :: right) cells := by
  cases cells <;> rfl

theorem advance_input (cells sourceRight sourceLeft : List (Option Bool)) (machine : Machine.Configuration) :
    StraightLine.execute (List.replicate cells.length (.left .input))
      { machine with inputTape := FixedWidthCopy.backwardFrontier sourceRight (cells ++ sourceLeft) } =
      { machine with pc := machine.pc + cells.length, inputTape := FixedWidthCopy.backwardFrontier (cells.reverse ++ sourceRight) sourceLeft } := by
  induction cells generalizing sourceRight machine with
  | nil => simp [StraightLine.execute]
  | cons cell rest ih =>
      simp only [List.length_cons, List.replicate_succ, StraightLine.execute, List.cons_append,
        StraightLine.apply, Machine.Configuration.updateTape, Machine.Configuration.advance,
        backward_move]
      have h := ih (cell :: sourceRight) { machine with pc := machine.pc + 1 }
      rw [h]
      simp [List.reverse_cons, List.append_assoc]
      omega

theorem advance_output (cells sourceRight sourceLeft : List (Option Bool)) (machine : Machine.Configuration) :
    StraightLine.execute (List.replicate cells.length (.left .output))
      { machine with outputTape := FixedWidthCopy.backwardFrontier sourceRight (cells ++ sourceLeft) } =
      { machine with pc := machine.pc + cells.length, outputTape := FixedWidthCopy.backwardFrontier (cells.reverse ++ sourceRight) sourceLeft } := by
  induction cells generalizing sourceRight machine with
  | nil => simp [StraightLine.execute]
  | cons cell rest ih =>
      simp only [List.length_cons, List.replicate_succ, StraightLine.execute, List.cons_append,
        StraightLine.apply, Machine.Configuration.updateTape, Machine.Configuration.advance, backward_move]
      have h := ih (cell :: sourceRight) { machine with pc := machine.pc + 1 }
      rw [h]
      simp [List.reverse_cons, List.append_assoc]
      omega

end CryptoOracle.Interactive.BackwardFieldCopy
