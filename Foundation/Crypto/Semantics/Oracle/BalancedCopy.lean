import Foundation.Crypto.Semantics.Oracle.StraightLine
import Foundation.Crypto.Semantics.Oracle.PacketWriter

/-! A single finite caller code reads its plaintext from the input tape.
The two bit branches have identical durations. Copying ends at a genuine
call instruction, rather than inserting a synthetic halted configuration. -/
namespace CryptoOracle.Interactive.BalancedCopy
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code :=
  [.call,
   .native (.branch .input 11 2 5),
   .native (.write .output false), .native (.jump 4), .native (.jump 8),
   .native (.write .output true), .native (.jump 7), .native (.jump 8),
   .native (.moveRight .input), .native (.moveRight .output), .native (.jump 1),
   .native (.erase .output),
   .native (.moveLeft .input), .native (.branch .input 16 14 14),
   .native (.moveLeft .output), .native (.jump 12),
   .native (.moveRight .input), .call, .native .halt]

def copied (bit : Bool) (machine : Machine.Configuration) : Machine.Configuration :=
  { machine with
    pc := 1
    inputTape := machine.inputTape.moveRight
    outputTape := (machine.outputTape.write (some bit)).moveRight }

def rewound (machine : Machine.Configuration) : Machine.Configuration :=
  { machine with pc := 12, inputTape := machine.inputTape.moveLeft, outputTape := machine.outputTape.moveLeft }

variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))

theorem copy_bit (bit : Bool) (machine : Machine.Configuration)
    (hPc : machine.pc = 1) (hActive : machine.halted = false)
    (hBit : machine.inputTape.current = some bit) :
    TimedExecution.eval (OneUseSource.step native code oracle) 7
      (.source false key ⟨state, .running machine, trace⟩) =
      PMF.pure (.source false key ⟨state, .running (copied bit machine), trace⟩) := by
  rcases machine with ⟨pc, inputTape, outputTape, halted⟩
  dsimp only at hPc hActive
  subst pc
  subst halted
  rcases inputTape with ⟨left, current, right⟩
  dsimp only at hBit
  subst current
  cases bit <;>
    simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, code, Machine.Instruction.next,
      Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
      Machine.Tape.write, copied, PMF.pure_map]

theorem rewind_bit (bit : Bool) (machine : Machine.Configuration)
    (inputLeft outputLeft : List (Option Bool))
    (hPc : machine.pc = 12) (hActive : machine.halted = false)
    (hInput : machine.inputTape.left = some bit :: inputLeft)
    (hOutput : machine.outputTape.left = some bit :: outputLeft) :
    TimedExecution.eval (OneUseSource.step native code oracle) 4
      (.source false key ⟨state, .running machine, trace⟩) =
      PMF.pure (.source false key ⟨state, .running (rewound machine), trace⟩) := by
  rcases machine with ⟨pc, inputTape, outputTape, halted⟩
  dsimp only at hPc hActive
  subst pc
  subst halted
  rcases inputTape with ⟨inputBefore, inputCurrent, inputRight⟩
  rcases outputTape with ⟨outputBefore, outputCurrent, outputRight⟩
  dsimp only at hInput hOutput
  subst inputBefore
  subst outputBefore
  cases bit <;>
    simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, code, Machine.Instruction.next,
      Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
      Machine.Tape.moveLeft, rewound, PMF.pure_map]

theorem packet_right (before after : List (Option Bool)) (bit : Bool) (bits : List Bool) :
    (RequestExport.packetTape before after (bit :: bits)).moveRight =
      RequestExport.packetTape (some bit :: before) after bits := by
  cases bits <;> rfl

theorem forward (before tail : List (Option Bool)) (bits : List Bool) (output : Machine.Tape) :
    TimedExecution.eval (OneUseSource.step native code oracle) (7 * bits.length + 2)
      (.source false key ⟨state, .running {
        pc := 1, inputTape := RequestExport.packetTape before tail bits, outputTape := output }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running {
        pc := 12
        inputTape := { left := bits.reverse.map some ++ before, right := tail }
        outputTape := { left := bits.reverse.map some ++ output.left, right := output.right.drop bits.length }
      }, trace⟩) := by
  induction bits generalizing before output with
  | nil =>
      simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, code, RequestExport.packetTape,
        Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Machine.Tape.write, PMF.pure_map]
  | cons bit bits ih =>
      rw [show 7 * (bit :: bits).length + 2 = 7 + (7 * bits.length + 2) by simp; omega,
        TimedExecution.eval_add, copy_bit native oracle key state trace bit _ rfl rfl rfl, PMF.pure_bind]
      simp only [copied, packet_right]
      rw [ih (some bit :: before) ((output.write (some bit)).moveRight)]
      cases ht : output.right <;> simp [Machine.Tape.write, Machine.Tape.moveRight, ht,
        List.reverse_cons, List.map_append, List.append_assoc]

def atHead (before cells : List (Option Bool)) : Machine.Tape :=
  ⟨before, cells.headD none, cells.tail⟩

theorem rewind (bits : List Bool) (inputCurrent outputCurrent : Option Bool)
    (inputRight outputRight : List (Option Bool)) :
    TimedExecution.eval (OneUseSource.step native code oracle) (4 * bits.length + 3)
      (.source false key ⟨state, .running {
        pc := 12
        inputTape := { left := bits.map some, current := inputCurrent, right := inputRight }
        outputTape := { left := bits.map some, current := outputCurrent, right := outputRight }
      }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running {
        pc := 17
        inputTape := atHead [none] (bits.reverse.map some ++ inputCurrent :: inputRight)
        outputTape := atHead [] (bits.reverse.map some ++ outputCurrent :: outputRight)
      }, trace⟩) := by
  induction bits generalizing inputCurrent outputCurrent inputRight outputRight with
  | nil =>
      simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, code, Machine.Instruction.next,
        Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
        Machine.Tape.moveLeft, Machine.Tape.moveRight, atHead, PMF.pure_map]
  | cons bit bits ih =>
      rw [show 4 * (bit :: bits).length + 3 = 4 + (4 * bits.length + 3) by simp; omega,
        TimedExecution.eval_add, rewind_bit native oracle key state trace bit _
          (bits.map some) (bits.map some) rfl rfl rfl rfl, PMF.pure_bind]
      simp only [rewound, List.map_cons, Machine.Tape.moveLeft]
      rw [ih (some bit) (some bit) (inputCurrent :: inputRight) (outputCurrent :: outputRight)]
      simp [atHead, List.reverse_cons, List.map_append, List.append_assoc]

theorem run (bits : List Bool) (inputTail outputRight : List (Option Bool)) (outputCurrent : Option Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) (11 * bits.length + 5)
      (.source false key ⟨state, .running {
        pc := 1
        inputTape := RequestExport.packetTape [] inputTail bits
        outputTape := { current := outputCurrent, right := outputRight }
      }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running {
        pc := 17
        inputTape := RequestExport.packetTape [none] inputTail bits
        outputTape := RequestExport.packetTape [] (outputRight.drop bits.length) bits
      }, trace⟩) := by
  rw [show 11 * bits.length + 5 = (7 * bits.length + 2) + (4 * bits.length + 3) by omega,
    TimedExecution.eval_add, forward, PMF.pure_bind]
  simp only [List.append_nil]
  have h := rewind native oracle key state trace bits.reverse none none inputTail (outputRight.drop bits.length)
  simpa only [List.length_reverse, List.reverse_reverse, RequestExport.packetTape, atHead] using h

end CryptoOracle.Interactive.BalancedCopy
