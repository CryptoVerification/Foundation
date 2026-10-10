import Foundation.Crypto.Semantics.Oracle.StraightLine
import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! Write and rewind an arbitrary request with original one-cell opcodes.
The old right-hand tail is retained beyond the overwritten request region.
No bulk tape replacement or free reset is an executed operation. -/
namespace CryptoOracle.Interactive.PacketWriter
open Foundation.Probability TimedExecution StraightLine

def forward (bits : List Bool) : List Action :=
  bits.flatMap (fun bit => [.write .output (some bit), .right .output])

def actions (bits : List Bool) : List Action :=
  forward bits ++ [.write .output none] ++ List.replicate bits.length (.left .output)

theorem length (bits : List Bool) : (actions bits).length = 3 * bits.length + 1 := by
  have hf : (forward bits).length = 2 * bits.length := by
    induction bits with
    | nil => rfl
    | cons bit bits ih => simp [forward, ih, Nat.mul_add]; omega
  simp [actions, hf]
  omega

theorem forward_erase (bits : List Bool) (machine : Machine.Configuration) :
    execute (forward bits ++ [.write .output none]) machine =
      { machine with
        pc := machine.pc + (2 * bits.length + 1)
        outputTape := {
          left := bits.reverse.map some ++ machine.outputTape.left
          right := machine.outputTape.right.drop bits.length } } := by
  induction bits generalizing machine with
  | nil => simp [forward, execute, apply, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Machine.Tape.write]
  | cons bit bits ih =>
      simp only [forward, List.flatMap_cons, List.cons_append, List.nil_append, execute]
      simp only [forward] at ih
      rw [ih]
      cases ht : machine.outputTape.right <;>
        simp [apply, Machine.Configuration.updateTape, Machine.Configuration.advance, Machine.Tape.write,
          Machine.Tape.moveRight, ht, List.reverse_cons, List.map_append, List.append_assoc,
          Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem writes_packet (bits : List Bool) (machine : Machine.Configuration) :
    execute (actions bits) machine =
      { machine with
        pc := machine.pc + (3 * bits.length + 1)
        outputTape := RequestExport.packetTape machine.outputTape.left
          (machine.outputTape.right.drop bits.length) bits } := by
  unfold actions
  rw [execute_append, forward_erase]
  have h := rewind_output (bits.map some) machine.outputTape.left
    (machine.outputTape.right.drop bits.length) none
    { machine with pc := machine.pc + (2 * bits.length + 1) }
  rw [show 3 * bits.length = 2 * bits.length + bits.length by omega]
  simpa [List.length_map, List.map_reverse, RequestExport.packetTape, rewindOutputTape,
    Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end CryptoOracle.Interactive.PacketWriter
