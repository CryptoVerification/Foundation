import Foundation.Constructions.ElGamal.MachineMultiplication
import Foundation.Examples.MachinePolynomialTime
import Foundation.Machine.GuessStatePreparation

namespace Foundation.Examples.MultiplyPreparation

open Machine Machine.GuardedCompiler

-- Runtime safety is independent of valid DDH/choose fields. These traces
-- use the actual native scans and framing instructions on retained tapes,
-- including internal blanks or dirty output cells.
example (input output : Tape) :
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor seekStoredInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output :=
  seekStoredInputScratch_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 200 * (input.cells + output.cells) + 200 ∧
      RunsFor writeFrame
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := writeFrame_terminates_from_anyTape _ _

-- The false delimiter is temporarily changed by real instructions and is
-- restored afterwards, together with the exact input head and stored tail.
example (before output tail : List (Option Bool)) (bits : List Bool) (blanks : Nat) :
    (writeFrameAfterFalseFinish before output tail bits blanks).inputTape =
      (writeFrameAfterFalseStart before output tail bits blanks).inputTape := rfl

-- Empty payloads still have a frame. Explicit unused blanks remain in the
-- returned configuration; the routine does not normalize either tape.
example : evalConfigWithin writeFrameAfterFalse
    (writeFrameAfterFalseStart [some true] [some false] [some true, none] [] 12)
    (writeFrameAfterFalseSteps []) =
      PMF.pure (writeFrameAfterFalseFinish [some true] [some false] [some true, none] [] 12) :=
  writeFrameAfterFalse_eval _ _ _ _ _

example : (writeFrameAfterFalseFinish [some true] [some false] [some true, none] [] 12).outputTape =
    { left := [some false, some false], right := List.replicate 11 none } := rfl

-- Saved challenge data remains behind the selected message and the two
-- separators while the message frame is appended to the public prefix.
example (challenge : Bool) (publicBits message : List Bool) :
    (frameSavedMessageFinish [] [some challenge] publicBits message 50).outputTape.left =
      (publicBits ++ frame message).reverse.map some ++
        none :: none :: message.reverse.map some ++ [none, some challenge] := rfl

example (challenge : Bool) (publicBits message : List Bool) :
    evalConfigWithin frameSavedMessage
      (frameSavedMessageStart [] [some challenge] publicBits message 50)
      (frameSavedMessageSteps publicBits message) =
      PMF.pure (frameSavedMessageFinish [] [some challenge] publicBits message 50) :=
  frameSavedMessage_eval _ _ _ _ _

-- Both operands are assembled from retained caller data. The selected
-- message precedes the final DDH component, including when either is empty.
example (before saved padding : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) :
    (prepareMultiplyOperandsFinish before saved padding n instanceBits first second last
      reply canonical selected).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last).reverse.map some ++
          none :: none :: selected.reverse.map some ++ none :: saved,
        right := List.replicate (instanceBits.length + 1 - (2*last.length + 1)) none } :=
  prepareMultiplyOperandsFinish_output _ _ _ _ _ _ _ _ _ _ _

-- This invokes the native call preparer on the actual returned operand
-- configuration. No fresh initial configuration supplies the request.
example (before saved : List (Option Bool)) (n : Nat)
    (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    evalConfigWithin prepareStoredCall
      ((prepareMultiplyOperandsFinish before saved (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (prepareStoredCallSteps last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)) =
      PMF.pure (prepareStoredCallFinish
        (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: saved) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2*last.length + 1))) :=
  prepareMultiplyOperandsFinish_call_eval _ _ _ _ _ _ _ _ _ _ _

-- A genuinely random source returns its fair bit through the actual
-- guarded call. The observer removes saved caller bits only mathematically;
-- the continuation must still inspect or move those cells natively.
example (challenge : Bool) :
    (evalConfigWithin (storedCallCompile Machine.Examples.randomOutputBit)
      (prepareStoredCallStart [some challenge] [] [] [true] [false] [] [] 4 9)
      (storedCallTraceBudget (fun _ => 2) [] [true] [false] [] [])).map
        (fun c => (c.halted, c.inputTape.bits.drop 3)) =
      Foundation.Probability.sampleBit.map (fun bit => (true, [bit])) := by
  have h := storedCallCompile_evalResult Machine.Examples.randomOutputBit
    [some challenge] [] [] [true] [false] [] [] 4 9 (fun _ => 2)
    (Machine.Examples.randomOutputBit_haltsWithin)
  simpa using h.trans (by
    rw [Machine.Examples.randomOutputBit_eval, PMF.map_comp]
    rfl)

example (q : Nat → Nat) (first second third fourth request : List Bool) :
    storedCallTraceBudget q first second third fourth request ≤
      150*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := storedCallTraceBudget_bound _ _ _ _ _ _

-- A returned empty result is framed as one false bit by the native
-- continuation, after the source halt and with nonempty stored caller data.
example :
    (evalConfigWithin (storedFramedCallCompile Machine.Examples.haltImmediately)
      (prepareStoredCallStart [some true] [some false] [true, false] [] [true] [] [] 7 9)
      (storedFramedCallTraceBudget (fun _ => 1) [true, false] [] [true] [] [])).map
        (fun c => (c.halted, c.outputTape.left.getD 0 none)) =
      PMF.pure (true, some false) := by
  have hCorrect : evalWithin Machine.Examples.haltImmediately [] 1 = PMF.pure (some []) := by
    simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
      Machine.Examples.haltImmediately, Configuration.initial, Configuration.outputBits,
      Tape.bits, PMF.pure_bind, PMF.pure_map]
  have h := storedFramedCallCompile_evalFrameCells Machine.Examples.haltImmediately
    [some true] [some false] [true, false] [] [true] [] [] [] 7 9 (fun _ => 1)
    (Machine.Examples.haltImmediately_haltsWithin []) hCorrect
  have hCell := congrArg
    (fun law : PMF (Bool × (Fin (frame []).length → Option Bool)) =>
      law.map (fun result => (result.1, result.2 ⟨0, by decide⟩))) h
  simpa [PMF.map_comp, PMF.pure_map, Function.comp_def, frame] using hCell

-- Native guess-state restoration reaches the empty state at its actual
-- blank separator. Selected-message scratch and product bits remain after
-- that separator, and the product frame on the other tape is unchanged.
example (output : Tape) :
    evalConfigWithin prepareGuessState
      (prepareGuessStateStart [some true, none, some false] [none, none]
        [true] [false] [] [true] [false, true] output)
      (prepareGuessStateSteps [true] [false] [] [true] [false, true]) =
      PMF.pure (prepareGuessStateFinish [some true, none, some false] [none, none]
        [true] [false] [] [true] [false, true] output) := prepareGuessState_eval _ _ _ _ _ _ _ _

example (output : Tape) :
    (prepareGuessStateFinish [some true] [] [true] [false] [] [true] [false, true] output).inputTape.current = none := rfl

example (before padding : List (Option Bool)) (first second state selected product : List Bool) (output : Tape) :
    (prepareGuessStateFinish before padding first second state selected product output).outputTape = output := rfl

example (q : Nat → Nat) (first second third fourth request : List Bool) :
    storedFramedCallTraceBudget q first second third fourth request ≤
      225*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := storedFramedCallTraceBudget_bound _ _ _ _ _ _


-- Native preparation also stops on malformed retained layouts. The actual
-- intermediate tapes determine the cost; protocol correctness is separate.
example (input output : Tape) :
    ∃ finish used, used ≤ 100000 * (input.cells + output.cells) + 100000 ∧
      RunsFor writeFrameAfterFalse
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := writeFrameAfterFalse_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 200000000 * (input.cells + output.cells) + 200000000 ∧
      RunsFor prepareMultiplyMessage
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareMultiplyMessage_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000 * (input.cells + output.cells) + 1000000000000000000 ∧
      RunsFor prepareMultiplyOperands
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareMultiplyOperands_terminates_from_anyTape _ _

example (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := prepareStoredCall_terminates_from_anyTape _ _

end Foundation.Examples.MultiplyPreparation
