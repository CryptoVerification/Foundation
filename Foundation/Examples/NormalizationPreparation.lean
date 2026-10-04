import Foundation.Machine.NormalizationInvocation
import Foundation.Constructions.ElGamal.MachineNormalization
import Foundation.Examples.MachinePolynomialTime

namespace Foundation.Examples.NormalizationPreparation

open Machine
open GuardedCompiler

-- Contextual scans reuse the existing instructions. Their saved prefixes
-- may contain data bits and blanks, not merely unrepresented empty space.
example (before : List (Option Bool)) (n : Nat) (rest : List (Option Bool)) (output : Tape) :
    evalConfigWithin skipUnary (skipUnaryCellsStart before n rest output) (3 * n + 3) =
      PMF.pure (skipUnaryCellsFinish before n rest output) := skipUnaryCells_eval _ _ _ _

example (before saved : List (Option Bool)) (bits : List Bool) :
    (skipFrameCellsFinish before saved bits.length
      (bits.map some ++ [none, some true, some false])).inputTape.right = [some true, some false] := by
  rw [skipFrameCellsFinish_input before saved bits none [some true, some false]]

-- Counter scanning is safe on all finite input tapes once a real blank
-- protects the output prefix. A truncated payload may cross input blanks;
-- all such head moves are still counted by the native trace.
example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used afterOutput remaining,
      used ≤ 10 * input.cells + 5 ∧
      RunsFor skipFrame
        ({ inputTape := input, outputTape := { left := none :: saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remaining none } :=
  skipFrameCells_terminates_with_layout input saved blanks

example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used afterOutput remaining,
      used ≤ 100 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 100 ∧
      RunsFor writeFrame
        ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remaining none } :=
  writeFrame_terminates_with_layout input saved blanks

example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used savedInput afterOutput remaining,
      used ≤ 1000 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 1000 ∧
      RunsFor preparePublicPrefixContext
        ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = some true ∧
      finish.inputTape.left = savedInput ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remaining none } :=
  preparePublicPrefixContext_terminates_with_layout input saved blanks

-- These all-input assembly certificates establish the actual normalizer
-- request and its size. A caller-specific fresh-output invariant is still
-- required before the compiled normalizer may be invoked on arbitrary data.
example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used request beforeRequest,
      used ≤ 5000000 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 5000000 ∧
      RunsFor prepareNormalizationInput
        ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape.Equivalent { Tape.ofBits request with left := none :: beforeRequest } ∧
      request.length ≤ finish.outputTape.cells :=
  prepareNormalizationInput_terminates_with_request_layout input saved blanks

example (input : Tape) (saved : List (Option Bool)) (blanks : Nat) :
    ∃ finish used request beforeRequest,
      used ≤ 200000000 * (input.cells + ({ left := saved, right := List.replicate blanks none } : Tape).cells) + 200000000 ∧
      RunsFor prepareChooseNormalization
        ({ inputTape := input, outputTape := { left := saved, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape.Equivalent { Tape.ofBits request with left := none :: beforeRequest } ∧
      request.length ≤ finish.outputTape.cells :=
  prepareChooseNormalization_terminates_with_request_layout input saved blanks

-- The caller's actual separator supplies the additional fresh-output
-- invariant. Neither raw reply validity nor saved-prefix validity is used.
example (beforeInput saved : List (Option Bool)) (reply : List Bool)
    (inputBlanks outputBlanks : Nat) :
    ∃ finish used sourceSaved targetSaved request,
      used ≤ 200000000 *
        (({ left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none } : Tape).cells +
         ({ left := saved, right := List.replicate outputBlanks none } : Tape).cells) + 200000000 ∧
      RunsFor prepareChooseNormalization
        ({ inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
           outputTape := { left := saved, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      (finish.resumeAt 0).Equivalent (packInputStart sourceSaved targetSaved request).swapTapes ∧
      request.length ≤ finish.outputTape.cells :=
  prepareChooseNormalization_terminates_with_guarded_layout beforeInput saved reply inputBlanks outputBlanks

example (coefficient degree : Nat) :
    PolynomiallyBounded (normalizationRetainedBudget coefficient degree) :=
  normalizationRetainedBudget_polynomial coefficient degree

-- A randomized normalizer checks the universal branch conclusion on
-- arbitrary finite replies and retained prefixes, including empty replies.
example (beforeInput saved : List (Option Bool)) (reply : List Bool)
    (inputBlanks outputBlanks : Nat) :
    let initial : Configuration :=
      { inputTape := { left := reply.reverse.map some ++ none :: beforeInput, right := List.replicate inputBlanks none },
        outputTape := { left := saved, right := List.replicate outputBlanks none } }
    ∀ finish, PaddedRunsFor (normalizeChooseCompile Machine.Examples.randomOutputBit) initial finish
      (normalizationRetainedBudget 2 0 (sourceStorage initial)) → finish.halted = true :=
  normalizeChooseCompile_haltsFrom_retainedReply Machine.Examples.randomOutputBit 2 0
    (fun input => by simpa using Machine.Examples.randomOutputBit_haltsWithin_any input)
    beforeInput saved reply inputBlanks outputBlanks

-- Framing an empty reply still writes its false length terminator, with
-- the old caller data and the following input data retained physically.
example : evalConfigWithin writeFrame
    (writeFrameContextStart [some true] [some false] [some true, none, some false] []) 11 =
      PMF.pure (writeFrameContextFinish [some true] [some false] [some true, none, some false] []) :=
  writeFrameContext_eval _ _ _ _

example : (writeFrameContextFinish [some true] [some false] [some true] []).outputTape.left =
    [some false, some false] := rfl

example (bits : List Bool) :
    RunsFor writeFrame (writeFrameContextStart [some true] [some false] [some true] bits)
      (writeFrameContextFinish [some true] [some false] [some true] bits)
      (writeFrameSteps bits) := writeFrameContext_runs _ _ _ _

example : prepareNormalizationInput.length = 81 := rfl
example : prepareChooseNormalization.length = 94 := rfl
example : prepareNormalizationInputSteps 0 [] [false] [] = 71 := rfl
example : prepareChooseNormalizationSteps 0 [] [false] [] = 91 := rfl

-- This trace starts at the actual end of the stored reply and DDH input.
-- Preparation restores the input head and frames the reply on the other
-- tape. The arbitrary source scratch prefix is preserved beyond a blank.
example (saved : List (Option Bool)) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) :
    evalConfigWithin prepareChooseNormalization
      (prepareChooseNormalizationStart saved n instanceBits bit tupleTail reply blanks)
      (prepareChooseNormalizationSteps n instanceBits (bit :: tupleTail) reply) =
      PMF.pure (prepareChooseNormalizationFinish saved n instanceBits bit tupleTail reply blanks) :=
  prepareChooseNormalization_eval _ _ _ _ _ _ _

example : (prepareChooseNormalizationFinish [some true, some false] 0 [] false [] [] 8).outputTape =
    { left := [none, some true, some false], current := some false,
      right := [some false, some false, none] } := rfl

-- A returned guarded source branch has this same layout, including its
-- explicit blank padding. No input/reply loading instruction is assumed.
example (source : Program) (sourceInput : List Bool) (n : Nat) (instanceBits : List Bool)
    (bit : Bool) (tupleTail : List Bool) (c : Configuration) :
    let saved := none :: (encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ [none]
    let returned := (rawResultFrom source sourceInput [none] saved c).swapTapes
    returned.resumeAt 0 = prepareChooseNormalizationStart returned.outputTape.left
      n instanceBits bit tupleTail c.outputBits (2 * c.outputTape.cells + 2 - c.outputBits.length) :=
  rawResultFrom_normalizationStart _ _ _ _ _ _ _

-- Plumbing sanity checks use an immediate halt, not a purported ElGamal
-- normalization algorithm. Preparation and guarded execution are charged.
example : (normalizeChooseCompile Machine.Examples.haltImmediately).length = 320 := by
  rw [normalizeChooseCompile_length]
  rfl
example : normalizationTraceBudget (fun _ => 1) 0 [] [false] [] = 682 := rfl

example : (evalConfigWithin (normalizeChooseCompile Machine.Examples.haltImmediately)
    (prepareChooseNormalizationStart [some true] 0 [] false [] [] 8) 682).map
      (fun c => (c.halted, c.inputTape.bits)) =
      PMF.pure (true, [false, false, true, false, false]) := by
  change (evalConfigWithin (normalizeChooseCompile Machine.Examples.haltImmediately)
    (prepareChooseNormalizationStart [some true] 0 [] false [] [] 8)
    (normalizationTraceBudget (fun _ => 1) 0 [] [false] [])).map
      (fun c => (c.halted, c.inputTape.bits)) = _
  rw [normalizeChooseCompile_evalOutput _ _ _ _ _ _ _ _ (fun _ => 1)
    (Machine.Examples.haltImmediately_haltsWithin _)]
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
    Machine.Examples.haltImmediately, Configuration.initial, Configuration.outputBits,
    Tape.bits, PMF.pure_bind, PMF.pure_map, encodeSecurityParameter, frame]

-- A supplied semantic certificate now applies after the native preparation
-- and guarded call. It covers every raw response, including malformed ones.
example
    {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
    {X : Nat → Type 1} {embed : ∀ n, X n → ElGamal.ConcreteInstance sampling n}
    {M : ElGamal.RepresentedSimulatorPrimitives sampling X embed}
    (N : ElGamal.RepresentedChooseNormalizer M) (saved : List (Option Bool))
    (n : Nat) (x : X n) (bit : Bool) (tupleTail rawReply : List Bool) (blanks : Nat) :
    (evalConfigWithin (normalizeChooseCompile N.program)
      (prepareChooseNormalizationStart saved n ((M.instanceCode n).encode x) bit tupleTail rawReply blanks)
      (normalizationTraceBudget N.budget n ((M.instanceCode n).encode x) (bit :: tupleTail) rawReply)).map
        (fun c => (c.halted, c.inputTape.bits)) =
      PMF.pure (true, encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
        frame (bit :: tupleTail) ++ rawReply ++
        ElGamal.normalizeChooseResponse (M.elementCode n x) (embed n x).params.generator rawReply) :=
  N.nativeContinuation_correct _ _ _ _ _ _ _

end Foundation.Examples.NormalizationPreparation
