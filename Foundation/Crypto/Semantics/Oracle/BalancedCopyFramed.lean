import Foundation.Crypto.Semantics.Oracle.BalancedCopy

/-! Copy a delimited input segment while retaining preceding input data.
The real blank delimiter stops rewind; the past is never reset or erased. -/
namespace CryptoOracle.Interactive.BalancedCopy
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))

theorem rewind_framed (past : List (Option Bool)) (bits : List Bool)
    (inputCurrent outputCurrent : Option Bool) (inputRight outputRight : List (Option Bool)) :
    TimedExecution.eval (OneUseSource.step native code oracle) (4 * bits.length + 3)
      (.source false key ⟨state, .running {
        pc := 12
        inputTape := { left := bits.map some ++ none :: past, current := inputCurrent, right := inputRight }
        outputTape := { left := bits.map some, current := outputCurrent, right := outputRight }
      }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running {
        pc := 17
        inputTape := atHead (none :: past) (bits.reverse.map some ++ inputCurrent :: inputRight)
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
          (bits.map some ++ none :: past) (bits.map some) rfl rfl rfl rfl, PMF.pure_bind]
      simp only [rewound, List.map_cons, List.cons_append, Machine.Tape.moveLeft]
      rw [ih (some bit) (some bit) (inputCurrent :: inputRight) (outputCurrent :: outputRight)]
      simp [atHead, List.reverse_cons, List.map_append, List.append_assoc]

theorem run_framed (past : List (Option Bool)) (bits : List Bool)
    (inputTail outputRight : List (Option Bool)) (outputCurrent : Option Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) (11 * bits.length + 5)
      (.source false key ⟨state, .running {
        pc := 1
        inputTape := RequestExport.packetTape (none :: past) inputTail bits
        outputTape := { current := outputCurrent, right := outputRight }
      }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running {
        pc := 17
        inputTape := RequestExport.packetTape (none :: past) inputTail bits
        outputTape := RequestExport.packetTape [] (outputRight.drop bits.length) bits
      }, trace⟩) := by
  rw [show 11 * bits.length + 5 = (7 * bits.length + 2) + (4 * bits.length + 3) by omega,
    TimedExecution.eval_add, forward, PMF.pure_bind]
  simp only [List.append_nil]
  have h := rewind_framed native oracle key state trace past bits.reverse none none inputTail (outputRight.drop bits.length)
  simpa only [List.length_reverse, List.reverse_reverse, RequestExport.packetTape, atHead] using h

end CryptoOracle.Interactive.BalancedCopy
