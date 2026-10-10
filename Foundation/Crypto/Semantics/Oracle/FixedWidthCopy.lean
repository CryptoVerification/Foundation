import Foundation.Crypto.Semantics.Oracle.StraightLine
import Foundation.Crypto.Semantics.Oracle.ResponseLoading

/-! Runtime copying of a fixed number of contiguous input bits. Unlike the
existing segment copier, the routine does not wait for a blank delimiter: the
following protocol marker can immediately follow the payload. Both branches
use five actual native transitions per bit. The finite code depends on width
and addresses only, never on payload values or oracle responses. -/
namespace CryptoOracle.Interactive.FixedWidthCopy
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Tape roles and movement direction are fixed at code construction.
The original copier is the input-to-output, rightward specialization. -/
def cellCodeWith (readOutput left : Bool) (base fault : Nat) : Code :=
  let source : TapeId := if readOutput then .output else .input
  let target : TapeId := if readOutput then .input else .output
  [.native (.branch source fault (base + 1) (base + 3)),
   .native (.write target false), .native (.jump (base + 5)),
   .native (.write target true), .native (.jump (base + 5)),
   .native (if left then .moveLeft source else .moveRight source),
   .native (if left then .moveLeft target else .moveRight target)]

/-- Blank input branches to the caller's explicit error address. -/
def cellCode (base fault : Nat) : Code := cellCodeWith false false base fault

def codeWith (readOutput left : Bool) (base : Nat) : Nat → Nat → Code
  | 0, _ => []
  | width + 1, fault => cellCodeWith readOutput left base fault ++ codeWith readOutput left (base + 7) width fault

@[simp] theorem cellCodeWith_length (readOutput left : Bool) (base fault : Nat) :
    (cellCodeWith readOutput left base fault).length = 7 := rfl

@[simp] theorem codeWith_length (readOutput left : Bool) (base width fault : Nat) :
    (codeWith readOutput left base width fault).length = 7 * width := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih => simp [codeWith, ih]; omega

/-- Every orientation uses only ordinary machine instructions. -/
theorem codeWith_native (readOutput left : Bool) (base width fault : Nat) :
    ∀ instruction ∈ codeWith readOutput left base width fault,
      ∃ native, instruction = .native native := by
  induction width generalizing base with
  | zero => simp [codeWith]
  | succ width ih =>
      intro instruction member
      simp only [codeWith, List.mem_append] at member
      rcases member with first | rest
      · simp only [cellCodeWith, List.mem_cons, List.not_mem_nil, or_false] at first
        rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      · exact ih _ instruction rest

def code (base : Nat) : Nat → Nat → Code
  | 0, _ => []
  | width + 1, fault => cellCode base fault ++ code (base + 7) width fault

@[simp] theorem cellCode_length (base fault : Nat) : (cellCode base fault).length = 7 := rfl

@[simp] theorem code_length (base width fault : Nat) : (code base width fault).length = 7 * width := by
  induction width generalizing base with
  | zero => simp [code]
  | succ width ih => simp [code, ih]; omega

/-- One bit is read by a branch instruction, then written and advanced.
The opaque oracle state and history are preserved. -/
theorem cell_run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (input : machine.inputTape.current = some bit) :
    TimedExecution.eval (Reification.timedStep (before ++ cellCode before.length fault ++ after) oracle) 5
      (⟨state, .running machine, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + 7, inputTape := machine.inputTape.moveRight, outputTape := (machine.outputTape.write (some bit)).moveRight }, trace⟩ := by
  cases bit <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, cellCode, cellCodeWith, pc, active, input,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, List.getElem?_append, Nat.add_assoc]

def frontier (left cells : List (Option Bool)) : Tape :=
  { ResponseLoading.fromCells cells with left := left }

theorem frontier_move (left cells : List (Option Bool)) (bit : Bool) :
    (frontier left (some bit :: cells)).moveRight = frontier (some bit :: left) cells := by
  cases cells <;> rfl

/-- Move across a known-length runtime region without requiring a blank
separator, retaining all input cells and both surrounding regions. -/
theorem advance_input (bits : List Bool) (before tail : List (Option Bool))
    (machine : Machine.Configuration) :
    StraightLine.execute (List.replicate bits.length (.right .input))
      { machine with inputTape := frontier before (bits.map some ++ tail) } =
      { machine with pc := machine.pc + bits.length, inputTape := frontier (bits.reverse.map some ++ before) tail } := by
  induction bits generalizing before machine with
  | nil => simp [StraightLine.execute]
  | cons bit bits ih =>
      simp only [List.length_cons, List.replicate_succ, StraightLine.execute, List.map_cons, List.cons_append]
      simp only [StraightLine.apply, Machine.Configuration.updateTape, Machine.Configuration.advance,
        frontier_move]
      simpa [Machine.Configuration.advance, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (some bit :: before) machine.advance

/-- The same region traversal on the output tape, preserving its suffix. -/
theorem advance_output (bits : List Bool) (before tail : List (Option Bool))
    (machine : Machine.Configuration) :
    StraightLine.execute (List.replicate bits.length (.right .output))
      { machine with outputTape := frontier before (bits.map some ++ tail) } =
      { machine with pc := machine.pc + bits.length, outputTape := frontier (bits.reverse.map some ++ before) tail } := by
  induction bits generalizing before machine with
  | nil => simp [StraightLine.execute]
  | cons bit bits ih =>
      simp only [List.length_cons, List.replicate_succ, StraightLine.execute, List.map_cons, List.cons_append]
      simp only [StraightLine.apply, Machine.Configuration.updateTape, Machine.Configuration.advance,
        frontier_move]
      simpa [Machine.Configuration.advance, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (some bit :: before) machine.advance

/-- Copy a runtime payload and retain its exact surrounding input cells.
Both tape prefixes are kept; no free tape reconstruction or reset is used. -/
theorem run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (beforeInput beforeOutput tail : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ code before.length bits.length fault ++ after) oracle)
      (5 * bits.length)
      (⟨state, .running { pc := before.length, inputTape := frontier beforeInput (bits.map some ++ tail), outputTape := { left := beforeOutput } }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + 7 * bits.length, inputTape := frontier (bits.reverse.map some ++ beforeInput) tail, outputTape := { left := bits.reverse.map some ++ beforeOutput } }, trace⟩ := by
  induction bits generalizing before beforeInput beforeOutput with
  | nil => simp [code, TimedExecution.eval]
  | cons bit bits ih =>
      rw [show 5 * (bit :: bits).length = 5 + 5 * bits.length by simp; omega,
        TimedExecution.eval_add]
      have hc := cell_run oracle state trace before
        (code (before.length + 7) bits.length fault ++ after) fault
        { pc := before.length, inputTape := frontier beforeInput ((bit :: bits).map some ++ tail), outputTape := { left := beforeOutput } } bit rfl rfl rfl
      simp only [List.length_cons, code, List.append_assoc] at ⊢
      simp only [List.append_assoc] at hc
      rw [hc, PMF.pure_bind]
      simp only [List.map_cons, List.cons_append, frontier_move, Tape.write]
      simp only [Tape.moveRight]
      have h := ih (before ++ cellCode before.length fault) (some bit :: beforeInput) (some bit :: beforeOutput)
      simp only [List.length_append, cellCode_length, List.append_assoc] at h
      rw [h]
      simp [List.reverse_cons, List.map_append, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

/-- The old finite code is definitionally unchanged at each cell. -/
theorem code_eq_with (base width fault : Nat) :
    code base width fault = codeWith false false base width fault := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih => simp only [code, codeWith, cellCode, ih]

/-- One leftward copy from the output tape to the input tape. -/
theorem backward_cell_run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (input : machine.outputTape.current = some bit) :
    TimedExecution.eval (Reification.timedStep (before ++ cellCodeWith true true before.length fault ++ after) oracle) 5
      (⟨state, .running machine, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + 7, inputTape := (machine.inputTape.write (some bit)).moveLeft, outputTape := machine.outputTape.moveLeft }, trace⟩ := by
  cases bit <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, cellCodeWith, pc, active, input,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, List.getElem?_append, Nat.add_assoc]

/-- A physical tape whose next cells are traversed toward the left. -/
def backwardFrontier (right cells : List (Option Bool)) : Tape :=
  { left := cells.tail, current := cells.headD none, right := right }

theorem backwardFrontier_move (right cells : List (Option Bool)) (bit : Bool) :
    (backwardFrontier right (some bit :: cells)).moveLeft = backwardFrontier (some bit :: right) cells := by
  cases cells <;> rfl

/-- Copy a runtime region toward the left into fresh left-hand cells. The
source's arbitrary remaining prefix and both right-hand regions survive. -/
theorem backward_run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (inputRight outputRight tail : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ codeWith true true before.length bits.length fault ++ after) oracle)
      (5 * bits.length)
      (⟨state, .running { pc := before.length, inputTape := { right := inputRight }, outputTape := backwardFrontier outputRight (bits.map some ++ tail) }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + 7 * bits.length, inputTape := { right := bits.reverse.map some ++ inputRight }, outputTape := backwardFrontier (bits.reverse.map some ++ outputRight) tail }, trace⟩ := by
  induction bits generalizing before inputRight outputRight with
  | nil => simp [codeWith, TimedExecution.eval]
  | cons bit bits ih =>
      rw [show 5 * (bit :: bits).length = 5 + 5 * bits.length by simp; omega,
        TimedExecution.eval_add]
      have hc := backward_cell_run oracle state trace before
        (codeWith true true (before.length + 7) bits.length fault ++ after) fault
        { pc := before.length, inputTape := { right := inputRight }, outputTape := backwardFrontier outputRight ((bit :: bits).map some ++ tail) } bit rfl rfl rfl
      simp only [List.length_cons, codeWith, List.append_assoc] at ⊢
      simp only [List.append_assoc] at hc
      rw [hc, PMF.pure_bind]
      simp only [List.map_cons, List.cons_append]
      rw [backwardFrontier_move]
      simp only [Tape.write, Tape.moveLeft]
      have h := ih (before ++ cellCodeWith true true before.length fault)
        (some bit :: inputRight) (some bit :: outputRight)
      simp only [List.length_append, cellCodeWith_length, List.append_assoc] at h
      rw [h]
      simp [List.reverse_cons, List.map_append, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

end CryptoOracle.Interactive.FixedWidthCopy
