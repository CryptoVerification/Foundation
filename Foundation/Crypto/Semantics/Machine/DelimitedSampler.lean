import Foundation.Crypto.Semantics.Machine.LeftFrame
import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! Exact random-bit generation from a blank-delimited marker block.
The input suffix after the delimiter is arbitrary and is preserved verbatim.
Saved cells on either left frontier are preserved by the common frame rule.
In particular an explicitly represented terminal blank need not be normalized
away before reusing the fixed sampler code. -/
namespace Machine.OneTimePad
open Foundation.Probability Foundation.Symmetric
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- Represent the delimiter explicitly even for a nonempty marker block. -/
def delimitedTape (remaining : List Bool) (suffix : List (Option Bool)) : Tape :=
  match remaining with
  | [] => {right := suffix}
  | bit :: rest => {current := some bit, right := rest.map some ++ none :: suffix}

def delimitedState (pastInput pastKey remaining : List Bool) (suffix : List (Option Bool)) : Configuration :=
  { inputTape := {delimitedTape remaining suffix with left := pastInput.reverse.map some}
    outputTape := {left := pastKey.reverse.map some} }

def delimitedFinish (pastInput pastKey : List Bool) (suffix : List (Option Bool)) : Configuration :=
  { pc := 5
    inputTape := {left := pastInput.reverse.map some, right := suffix}
    outputTape := {left := pastKey.reverse.map some}
    halted := true }

theorem keygen_delimited_iteration (pastInput pastKey rest : List Bool) (marker : Bool)
    (suffix : List (Option Bool)) :
    evalConfigWithin keygen (delimitedState pastInput pastKey (marker :: rest) suffix) 5 =
      sampleBit.map (fun bit => delimitedState (pastInput ++ [marker]) (pastKey ++ [bit]) rest suffix) := by
  cases marker <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, keygen, delimitedState, delimitedTape,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, PMF.bind_map,
      PMF.map_comp, Function.comp_def, List.reverse_append]
  all_goals
    change sampleBit.bind _ = sampleBit.map _
    rw [PMF.map]
    congr 1
    funext bit
    cases bit <;> simp [stepPMF, next, keygen, delimitedState, delimitedTape, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.write, Tape.moveRight, List.reverse_append]

/-- Full physical exit distribution, including the unused input suffix. -/
theorem keygen_delimited_run (pastInput pastKey remaining : List Bool) (suffix : List (Option Bool)) :
    evalConfigWithin keygen (delimitedState pastInput pastKey remaining suffix) (5 * remaining.length + 2) =
      (uniform (Bits remaining.length)).map (fun key =>
        delimitedFinish (pastInput ++ remaining) (pastKey ++ key.toList) suffix) := by
  induction remaining generalizing pastInput pastKey with
  | nil => simp [evalConfigWithin, stepPMF, next, keygen, delimitedState, delimitedTape, delimitedFinish,
      Instruction.next, Configuration.tape, Bits.toList, PMF.map_const, Function.const_def]
  | cons marker rest ih =>
      rw [show 5 * (marker :: rest).length + 2 = 5 + (5 * rest.length + 2) by simp; omega,
        evalConfigWithin_add, keygen_delimited_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih, List.length_cons]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def,
        Bits.toList, List.ofFn_succ, List.append_assoc]

/-- Arbitrary saved physical cells are retained, without changing the code. -/
theorem keygen_delimited_framed_run (pastInput pastKey remaining : List Bool)
    (suffix inputFrame outputFrame : List (Option Bool)) :
    evalConfigWithin keygen
      ((delimitedState pastInput pastKey remaining suffix).frameLeft inputFrame outputFrame)
      (5 * remaining.length + 2) =
      (uniform (Bits remaining.length)).map (fun key =>
        (delimitedFinish (pastInput ++ remaining) (pastKey ++ key.toList) suffix).frameLeft inputFrame outputFrame) := by
  rw [evalConfigWithin_frameLeft keygen _ (by intro tape; cases tape <;> decide),
    keygen_delimited_run, PMF.map_comp]
  rfl

end Machine.OneTimePad
