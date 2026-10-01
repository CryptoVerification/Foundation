import Foundation.Machine.NormalizedMessageSelection
import Foundation.Machine.MultiplyPrefixPreparation
import Foundation.Constructions.ElGamal.MachineNormalization

namespace Foundation.Examples.MessageSelection

open Machine
open GuardedCompiler
open Foundation.Probability

-- These are finite native instructions, including one fair random-bit
-- instruction in the selector. No field, parameter or instance enters code.
example : skipDelimited.length = 7 := rfl
example : selectMessage.length = 17 := rfl
example : prepareMessageSelection.length = 24 := rfl
example : copyMessageField.length = 20 := rfl
example : prepareSelectedMessage.length = 47 := rfl
example : restoreStoredInput.length = 18 := rfl
example : prepareMultiplyPrefix.length = 64 := rfl

-- Runtime statements use every finite tape, independently of the valid
-- delimiter/canonical-response assumptions in the semantic examples below.
example (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor skipDelimited
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (4 * input.cells + 7)) : finish.halted = true :=
  skipDelimited_haltsFrom_anyTape _ _ _ run

example (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor copyMessageField
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (8 * input.cells + 9)) : finish.halted = true :=
  copyMessageField_haltsFrom_anyTape _ _ _ run

example : PolynomialTime prepareSelectedMessage := prepareSelectedMessage_polynomialTime

-- The same all-input proof also retains the physical fresh output region
-- needed by subsequent native multiplication-request construction.
example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
      finish (400 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 500)) :
    ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } :=
  prepareSelectedMessage_output_layout_anyTape _ _ _ _ run

example (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor restoreStoredInput
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (100 * (input.cells + output.cells) + 100)) : finish.halted = true :=
  restoreStoredInput_haltsFrom_anyTape _ _ _ run

example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 200000 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 200000 ∧
      RunsFor prepareMultiplyPrefix
        ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } :=
  prepareMultiplyPrefix_terminates_with_output_layout _ _ _

-- A dangling true delimiter marker and internal blanks need not describe
-- any pair of messages. Both actual random branches still halt.
example (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      ({ inputTape := { left := [none, some true], current := some false, right := [some true, none, some false] },
         outputTape := { left := [some true], right := [none] } } : Configuration)
      finish (400 * (6 + 3) + 500)) : finish.halted = true := by
  exact prepareSelectedMessage_haltsFrom_anyTape _ _ finish run

-- No canonical-output premise is imposed on the normalizer's branch.
example (normalizer : Program) (input : List Bool)
    (beforeInput saved : List (Option Bool)) (c : Configuration) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: saved) c).swapTapes
    ∀ finish, PaddedRunsFor prepareSelectedMessage (returned.resumeAt 0) finish
      (400 * (returned.inputTape.cells + returned.outputTape.cells) + 500) →
      finish.halted = true :=
  selectNormalizedMessage_haltsFrom _ _ _ _ _

example (normalizer : Program) (input : List Bool)
    (beforeInput saved : List (Option Bool)) (c : Configuration) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: saved) c).swapTapes
    ∀ finish, PaddedRunsFor prepareSelectedMessage (returned.resumeAt 0) finish
      (400 * (returned.inputTape.cells + returned.outputTape.cells) + 500) →
      ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } :=
  selectNormalizedMessage_output_layout _ _ _ _ _

-- The following separator and data cells are preserved even when a field
-- is empty. This is not restricted to a trailing all-blank tape region.
example : evalConfigWithin skipDelimited
    (skipDelimitedStart [some true] [] [none, some true, some false] { left := [some false] }) 3 =
    PMF.pure (skipDelimitedFinish [some true] [] [none, some true, some false] { left := [some false] }) :=
  skipDelimited_eval _ _ _ _

example : (skipDelimitedFinish [some true] [] [none, some true, some false]
    { left := [some false] }).inputTape =
    { left := [some false, some true], right := [some true, some false] } := by
  rw [skipDelimitedFinish_layout]
  rfl

example (beforeInput beforeOutput : List (Option Bool)) (first second state : List Bool) (blanks : Nat) :
    evalConfigWithin prepareSelectedMessage
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      (prepareSelectedMessageSteps first second state) =
      sampleBit.map (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks) :=
  prepareSelectedMessage_eval _ _ _ _ _ _

-- Saved bits remain behind an actual blank, and the parser status bit has
-- been erased at the output head. The unselected message/state are retained.
example : (prepareSelectedMessageFinish [some true] [some false]
    [false, true] [true] [false] 5 false).outputTape =
    { left := [some true, some false, none, some false, some false], right := [none] } := rfl

example : (prepareSelectedMessageFinish [some true] [some false]
    [false, true] [true] [false] 5 true).outputTape =
    { left := [some true, none, some true, some false], right := [none] } := rfl

example : prepareSelectedMessageSteps [false, true] [true] [false] = 79 := rfl
example : prepareSelectedMessageSteps [] [] [] = 33 := rfl

-- Observe the two branches of the real machine's execution. The saved
-- prefix contributes the initial true bit; the next bit is the very same
-- fair bit which selects the following raw message code.
example : (evalConfigWithin prepareSelectedMessage
    (prepareMessageSelectionStart [some true, none, some false] [some true]
      [false, true] [true] [false] 5) 79).map
      (fun c => (c.halted, c.outputBits)) =
    sampleBit.map (fun bit => (true, [true, bit] ++ if bit then [true] else [false, true])) := by
  change (evalConfigWithin prepareSelectedMessage
    (prepareMessageSelectionStart [some true, none, some false] [some true]
      [false, true] [true] [false] 5)
    (prepareSelectedMessageSteps [false, true] [true] [false])).map _ = _
  rw [prepareSelectedMessage_eval, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> simp [prepareSelectedMessageFinish, copyMessageFieldFinish,
    Configuration.outputBits, readDelimitedContextFinish, Tape.bits]

-- Empty canonical message codes are copied successfully, and the machine
-- still samples and retains its native challenge bit in both branches.
example : (evalConfigWithin prepareSelectedMessage
    (prepareMessageSelectionStart [] [] [] [] [] 4) 33).map
      (fun c => (c.halted, c.outputBits)) = sampleBit.map (fun bit => (true, [bit])) := by
  change (evalConfigWithin prepareSelectedMessage
    (prepareMessageSelectionStart [] [] [] [] [] 4)
    (prepareSelectedMessageSteps [] [] [])).map _ = _
  rw [prepareSelectedMessage_eval, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> simp [prepareSelectedMessageFinish, copyMessageFieldFinish,
    Configuration.outputBits, readDelimitedContextFinish, Tape.bits]

example (beforeInput beforeOutput : List (Option Bool)) (first second state : List Bool)
    (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      finish (prepareSelectedMessageSteps first second state)) : finish.halted = true :=
  prepareSelectedMessage_haltsFrom _ _ _ _ _ _ _ run

-- This begins at the actual end of a guarded normalizer's copied output.
-- The layout equality supplies no free decoding, output initialization or
-- memory transfer. It also retains that normalizer's physical scratch prefix.
example (normalizer : Program) (input : List Bool) (beforeInput saved : List (Option Bool))
    (c : Configuration) (first second state : List Bool)
    (h : c.outputBits = canonicalMessageBits first second state) :
    let returned := (rawResultFrom normalizer input beforeInput (none :: saved) c).swapTapes
    evalConfigWithin prepareSelectedMessage (returned.resumeAt 0)
      (prepareSelectedMessageSteps first second state) =
      sampleBit.map (prepareSelectedMessageFinish saved returned.outputTape.left first second state
        (2 * c.outputTape.cells + 2 - c.outputBits.length)) :=
  selectNormalizedMessage_eval _ _ _ _ _ _ _ _ h

-- Returning to the earlier stored input preserves the entire other tape,
-- including the copied selected field and its saved native challenge.
example (before beforeOutput : List (Option Bool)) (original reply first second state : List Bool)
    (blanks : Nat) (bit : Bool) :
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
    evalConfigWithin restoreStoredInput (returned.resumeAt 0)
      (restoreStoredInputSteps original reply (selectedMessageConsumed first second bit)) =
      PMF.pure (restoreStoredInputFinish before original reply (selectedMessageConsumed first second bit)
        returned.inputTape.current returned.inputTape.right returned.outputTape) :=
  selectedMessage_restore_eval _ _ _ _ _ _ _ _ _

-- Even three empty stored blocks require real rewind/separator transitions.
example : evalConfigWithin restoreStoredInput
    (restoreStoredInputStart [some true] [] [] [] none [some false]
      { left := [none, some true, some false], right := [none] }) 15 =
    PMF.pure (restoreStoredInputFinish [some true] [] [] [] none [some false]
      { left := [none, some true, some false], right := [none] }) :=
  restoreStoredInput_eval _ _ _ _ _ _ _

example : (prepareMultiplyPrefixFinish [] [none, some true, some false]
    0 [] [] [] [] [true] none []).outputTape =
    { left := [some false, some false, none, none, some true, none, some true, some false] } := by
  rw [prepareMultiplyPrefixFinish_output]
  rfl

example (beforeInput beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits tupleTail reply consumed selected : List Bool) (current : Option Bool)
    (right : List (Option Bool)) :
    evalConfigWithin prepareMultiplyPrefix
      (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed) =
      PMF.pure (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right) :=
  prepareMultiplyPrefix_eval _ _ _ _ _ _ _ _ _ _

end Foundation.Examples.MessageSelection
