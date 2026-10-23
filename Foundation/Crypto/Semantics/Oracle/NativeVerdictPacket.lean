import Foundation.Crypto.Semantics.Oracle.NativeDeterministic

/-! Real native code materializes a mask of an existing verdict bit. Branch
cost is balanced. State/transcript are not machine inputs; input memory and
all cells left of the old verdict are retained. Entry/handoff is explicit. -/
namespace CryptoOracle.Interactive.NativeVerdictPacket
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def emit : List Bool → Code
  | [] => []
  | bit :: rest => .native (.moveRight .output) :: .native (.write .output bit) :: emit rest

def written : Tape → List Bool → Tape
  | tape, [] => tape
  | tape, bit :: rest => written (tape.moveRight.write (some bit)) rest

def start (base : Nat) (input output : Tape) : Machine.Configuration :=
  {pc := base, inputTape := input, outputTape := output}

def emitFinish (base : Nat) (input output : Tape) (bits : List Bool) : Machine.Configuration :=
  {pc := base + 2 * bits.length, inputTape := input, outputTape := written output bits}

def Located (code : Code) (base : Nat) (bits : List Bool) : Prop :=
  ∀ index (inside : index < bits.length),
    code[base + 2 * index]? = some (.native (.moveRight .output)) ∧
    code[base + 2 * index + 1]? = some (.native (.write .output bits[index]))

theorem emit_length (bits : List Bool) : (emit bits).length = 2 * bits.length := by
  induction bits <;> simp_all [emit]; omega

theorem emit_get (bits : List Bool) (index : Nat) (inside : index < bits.length) :
    (emit bits)[2 * index]? = some (.native (.moveRight .output)) ∧
    (emit bits)[2 * index + 1]? = some (.native (.write .output bits[index])) := by
  induction bits generalizing index with
  | nil => simp at inside
  | cons bit rest ih =>
      cases index with
      | zero => simp [emit]
      | succ index =>
          simpa [emit, Nat.mul_succ, Nat.add_assoc] using (ih index (by simpa using inside))

theorem located_append (before : Code) (bits : List Bool) (after : Code) :
    Located (before ++ emit bits ++ after) before.length bits := by
  intro index inside
  have bound : 2 * index + 1 < (emit bits).length := by rw [emit_length]; omega
  constructor
  · rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
    exact (emit_get bits index inside).1
  · rw [List.append_assoc, List.getElem?_append_right (by omega)]
    rw [show before.length + 2 * index + 1 - before.length = 2 * index + 1 by omega,
      List.getElem?_append_left bound]
    exact (emit_get bits index inside).2

theorem emit_checked (code : Code) (base : Nat) (input output : Tape) (bits : List Bool)
    (located : Located code base bits) :
    NativeDeterministic.run code (2 * bits.length) (start base input output) =
      some (emitFinish base input output bits) := by
  induction bits generalizing base output with
  | nil => simp [NativeDeterministic.run, emitFinish, written, start]
  | cons bit rest ih =>
      have first : code[base]? = some (.native (.moveRight .output)) ∧
          code[base + 1]? = some (.native (.write .output bit)) := by simpa using located 0 (by simp)
      have next : Located code (base + 2) rest := by
        intro index inside
        have step := located (index + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at step
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
      rw [show 2 * (bit :: rest).length = 2 + 2 * rest.length by simp; omega, NativeDeterministic.run_add]
      have head : NativeDeterministic.run code 2 (start base input output) =
          some (start (base + 2) input (output.moveRight.write (some bit))) := by
        simp [NativeDeterministic.run, NativeDeterministic.next?, start, first.1, first.2,
          Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
          Nat.add_assoc]
      rw [head, Option.bind_some, ih (base + 2) (output.moveRight.write (some bit)) next]
      congr 1
      simp [emitFinish, written, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

def code (mask : List Bool) : Code :=
  [.native (.branch .output 1 1 (2 * mask.length + 2))] ++
  emit (mask.map fun _ => false) ++ [.native (.jump (4 * mask.length + 3))] ++
  emit mask ++ [.native (.jump (4 * mask.length + 3)), .native .halt]

def result (mask : List Bool) (bit : Bool) : List Bool := mask.map (fun keep => keep && bit)

def finish (mask : List Bool) (input output : Tape) : Machine.Configuration :=
  {pc := 4 * mask.length + 3, inputTape := input,
    outputTape := written output (result mask (output.current.getD false)), halted := true}

theorem code_length (mask : List Bool) : (code mask).length = 4 * mask.length + 4 := by
  simp [code, emit_length]; omega

theorem result_length (mask : List Bool) (bit : Bool) : (result mask bit).length = mask.length := by
  simp [result]

end CryptoOracle.Interactive.NativeVerdictPacket
