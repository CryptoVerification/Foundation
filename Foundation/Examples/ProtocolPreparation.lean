import Foundation.Machine.ProtocolPrefix
import Foundation.Machine.Encoding
import Foundation.Machine.OppositeCall
import Foundation.Machine.ChoosePreparation
import Foundation.Machine.DDHChooseCall
import Foundation.Machine.ChooseInvocation
import Foundation.Examples.MachinePolynomialTime
import Foundation.Machine.PPT

namespace Foundation.Examples.ProtocolPreparation

open Machine

-- The security-parameter scan retains its input cells and arbitrary output data.
example (before : List (Option Bool)) (n : Nat) (rest : List Bool) (output : Tape) :
    evalConfigWithin skipUnary (skipUnaryStart before n rest output) (3 * n + 3) =
      PMF.pure (skipUnaryFinish before n rest output) := skipUnary_eval before n rest output

-- The missing terminator is included in the all-input, worst-case bound.
example : PolynomialTime skipUnary := skipUnary_polynomialTime
example : HaltsWithin skipUnary [true, true, true] 12 := skipUnary_haltsWithin _

-- Even caller data beyond the blank are preserved. The copying routine does
-- not follow the separator into the next field, nor erase saved prefixes.
example : (copySegmentFinish [some true] [some false] [some true, some false]
    [false, true] 4).inputTape.right = [some true, some false] := rfl
example (bits : List Bool) :
    RunsFor copyBitstring (copySegmentStart [some true] [some false] [some true] bits 4)
      (copySegmentFinish [some true] [some false] [some true] bits 4)
      (copyBitstringSteps bits) := copySegment_runs _ _ _ _ _

-- The native public-prefix routine really performs the erasure, rewind,
-- cell copies, and header restoration. For this fixture it takes 24 steps.
example : savePublicPrefixSteps [true, false] = 24 := rfl
example : evalConfigWithin savePublicPrefix
    (savePublicPrefixStart [true, false] [some false, some true] [some true] 4) 24 =
      PMF.pure (savePublicPrefixFinish [true, false] [some false, some true] [some true] 4) :=
  savePublicPrefix_eval _ _ _ _

-- Prefix assembly is forty actual finite instructions, independent of the
-- source adversary code, security parameter, and instance-family oracle.
example : prepareDDHPublicPrefix.length = 40 := rfl
-- The new runtime certificate covers every raw bitstring, including a
-- missing delimiter and a truncated frame. It does not certify the full
-- ElGamal simulator's all-input termination.
example : PolynomialTime prepareDDHPublicPrefix := prepareDDHPublicPrefix_polynomialTime
example (input : List Bool) :
    HaltsWithin prepareDDHPublicPrefix input (300 * input.length + 300) :=
  prepareDDHPublicPrefix_haltsWithin_anyInput input
example : HaltsWithin prepareDDHPublicPrefix [true, true, true] 1200 :=
  prepareDDHPublicPrefix_haltsWithin_anyInput _
example : HaltsWithin prepareDDHPublicPrefix [false, true, true, false] 1500 :=
  prepareDDHPublicPrefix_haltsWithin_anyInput _

-- Saving can stop safely even when previously retained tapes contain
-- internal blanks and the destination is not a fresh output region.
example (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat),
      used ≤ 20 * (input.cells + output.cells) + 33 ∧
      RunsFor savePublicPrefix
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := savePublicPrefix_terminates_from_anyTape input output

example (n : Nat) (instanceBits requestTail : List Bool) :
    evalConfigWithin prepareDDHPublicPrefix
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail))
      (prepareDDHPublicPrefixSteps n instanceBits) =
      PMF.pure (prepareDDHPublicPrefixFinish n instanceBits requestTail) :=
  prepareDDHPublicPrefix_eval _ _ _

-- Exact charged preparation of n=1 and the two-bit instance. Input request
-- cells remain present, while only the public prefix is on the output tape.
example : prepareDDHPublicPrefixSteps 1 [false, true] = 93 := rfl
example : (prepareDDHPublicPrefixFinish 1 [false, true] [false, true]).outputBits =
    [true, false, true, true, false, false, true] := by
  rw [prepareDDHPublicPrefix_output]
  rfl
example : (prepareDDHPublicPrefixFinish 1 [false, true] [false, true]).inputTape.bits =
    [true, false, true, true, false, false, true, true, false, true] := by
  rw [prepareDDHPublicPrefix_input]
  rfl

-- This is a valid-input preparation certificate, not an assertion that a
-- complete ElGamal simulator has already been compiled or proved PPT.
example (n : Nat) (instanceBits requestTail : List Bool) :
    HaltsWithin prepareDDHPublicPrefix
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail)
      (26 * (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail).length + 34) :=
  prepareDDHPublicPrefix_haltsWithin _ _ _

-- A canonical DDH triple always has a nonempty code, even when an element
-- encoding is empty. The trace therefore applies to the actual triple frame.
example {α : Type} (E : FiniteBitEncoding α) (x y z : α)
    (n : Nat) (instanceBits : List Bool) :
    evalConfigWithin prepareDDHPublicPrefix
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (E.triple.encode (x, y, z))))
      (prepareDDHPublicPrefixSteps n instanceBits) =
      PMF.pure (prepareDDHPublicPrefixFinish n instanceBits
        (List.replicate ((E.triple.encode (x, y, z)).length - 1) true ++
          false :: E.triple.encode (x, y, z))) := by
  apply prepareDDHPublicPrefix_framed_eval
  intro hEmpty
  have hLength := congrArg List.length hEmpty
  simp [FiniteBitEncoding.triple, FiniteBitEncoding.prod_encode_length] at hLength

-- Header generation counts payload bits through native reads. The extra
-- header bit accounts for the false choose tag; payload copying is a later
-- pass, rather than a framing operation hidden in this observation.
example : writeChooseHeader.length = 15 := rfl
example : PolynomialTime writeChooseHeader := writeChooseHeader_polynomialTime
example : HaltsWithin writeChooseHeader [true] 22 := writeChooseHeader_haltsWithin_anyInput _
example (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 7 * input.cells + 8 ∧
      RunsFor writeChooseHeader
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := writeChooseHeader_terminates_from_anyTape input output

-- Parser stopping remains available on retained tapes with an internal
-- blank before later caller data and with an arbitrary output region.
example (before : List (Option Bool)) (output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 8 * (before.length + 3) + 6 ∧
      RunsFor readDelimited
        ({ inputTape := { left := before, current := some true, right := [none, some false] },
           outputTape := output } : Configuration) finish used ∧ finish.halted = true := by
  simpa only [Tape.cells, List.length_cons, List.length_nil, Nat.add_assoc] using
    readDelimited_terminates_from_anyTape
      ({ left := before, current := some true, right := [none, some false] } : Tape) output

example : PolynomialTime assembleChooseField := assembleChooseField_polynomialTime
example (input : List Bool) :
    HaltsWithin assembleChooseField input (220 * input.length + 740) :=
  assembleChooseField_haltsWithin_anyInput input
example : PolynomialTime prepareDDHChooseRequest := prepareDDHChooseRequest_polynomialTime
example (input : List Bool) :
    HaltsWithin prepareDDHChooseRequest input (300000 * (input.length + 1)) :=
  prepareDDHChooseRequest_haltsWithin_anyInput input
example : PolynomialTime prepareDDHChooseCall := prepareDDHChooseCall_polynomialTime
example (input : List Bool) :
    HaltsWithin prepareDDHChooseCall input (20000000 * (input.length + 1)) :=
  prepareDDHChooseCall_haltsWithin_anyInput input

-- Physical layouts are proved for raw bitstrings, including an empty
-- input, a missing frame terminator, and truncated delimited payloads.
-- Arbitrary caller prefixes may contain internal blank cells.
example (before : List (Option Bool)) (input : List Bool) :
    ∃ finish used saved rest outputPrefix blanks,
      used ≤ 10 * input.length + 5 ∧
      RunsFor skipFrame
        ({ inputTape := { Tape.ofBits input with left := before } } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = { Tape.ofBits rest with left := saved } ∧
      finish.outputTape = { left := outputPrefix, right := List.replicate blanks none } :=
  skipFrame_terminates_with_layout before input

example (input : List Bool) :
    ∃ finish used saved rest outputPrefix blanks,
      used ≤ 300 * input.length + 300 ∧
      RunsFor prepareDDHPublicPrefix (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      finish.inputTape = { Tape.ofBits (true :: rest) with left := saved } ∧
      finish.outputTape = { left := outputPrefix, right := List.replicate blanks none } :=
  prepareDDHPublicPrefix_terminates_with_layout input

-- An exact branch trace transfers across redundant outer blanks with
-- the same number of actual transitions. This also applies to fair bits.
example (p : Program) (start finish other : Configuration) (used : Nat)
    (run : RunsFor p start finish used) (h : start.Equivalent other) :
    ∃ target, RunsFor p other target used ∧ finish.Equivalent target :=
  run.exists_equivalent h

example (before : List (Option Bool)) (field : List Bool) :
    ∃ finish used saved rest outputPrefix blanks,
      used ≤ 220 * (({ Tape.ofBits field with left := before } : Tape).cells + ({} : Tape).cells) + 300 ∧
      RunsFor assembleChooseField
        ({ inputTape := { Tape.ofBits field with left := before } } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape.Equivalent { Tape.ofBits rest with left := saved } ∧
      finish.outputTape.Equivalent { left := outputPrefix, right := List.replicate blanks none } :=
  assembleChooseField_terminates_with_layout before [] field 0

-- The complete front end also establishes a guarded source-call layout
-- on malformed inputs. Source time is bounded on every finite bitstring;
-- this certifies the choose stage, not the full simulator continuation.
example (input : List Bool) :
    ∃ finish used beforeInput beforeOutput sourceInput,
      used ≤ 20000000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseCall (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart beforeInput beforeOutput sourceInput).swapTapes ∧
      sourceInput.length ≤ finish.outputTape.cells :=
  prepareDDHChooseCall_terminates_with_layout input

-- The protected output prefix begins with a real blank on every input.
-- It remains available when the raw source response is returned and the
-- normalizer continuation rewinds the saved caller cells.
example (input : List Bool) :
    ∃ finish used beforeInput beforeOutput sourceInput,
      used ≤ 20000000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseCall (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart beforeInput (none :: beforeOutput) sourceInput).swapTapes ∧
      sourceInput.length ≤ finish.outputTape.cells :=
  prepareDDHChooseCall_terminates_with_separated_layout input

-- The all-input returned-state law also covers randomized source code.
-- This observation forgets only tape cells, rather than restricting which
-- malformed DDH requests the wrapper is allowed to receive.
example (source : Program) (q : Nat → Nat)
    (hSource : ∀ request : List Bool, HaltsWithin source request (q request.length))
    (input : List Bool) :
    ∃ (used : Nat) (sourceInput : List Bool),
      used ≤ 20000000 * (input.length + 1) ∧
      (evalConfigWithin (GuardedCompiler.chooseCompile source) (Configuration.initial input)
        (used + GuardedCompiler.rawTraceBudget q sourceInput.length + 1)).map Configuration.halted =
      (evalConfigWithin source (GuardedCompiler.preparedSource sourceInput) (q sourceInput.length)).map
        (fun _ => true) := by
  obtain ⟨used, sourceInput, _beforeInput, _beforeOutput, hBound, hLaw⟩ :=
    GuardedCompiler.chooseCompile_evalObservation_anyInput source q hSource input
      Configuration.halted (fun _ _ h => h.2.1)
  exact ⟨used, sourceInput, hBound, hLaw⟩

example : PolynomialTime (GuardedCompiler.chooseCompile Machine.Examples.randomOutputBit) :=
  GuardedCompiler.chooseCompile_polynomialTime_of_monomial _ 2 0
    (fun input => by
      simpa only [pow_zero, Nat.mul_one] using
        Machine.Examples.randomOutputBit_haltsWithin_any input)

-- The source's eventual polynomial bound is enlarged to a global
-- monomial before it is evaluated on generated, possibly malformed inputs.
example (source : Program) (hSource : PolynomialTime source) :
    PolynomialTime (GuardedCompiler.chooseCompile source) := by
  obtain ⟨q, hPolynomial, hHalts⟩ := hSource
  obtain ⟨coefficient, degree, hGlobal⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hPolynomial
  exact GuardedCompiler.chooseCompile_polynomialTime_of_monomial source coefficient degree
    (fun input => (hHalts input).mono (hGlobal input.length))

example : evalConfigWithin writeChooseHeader
    (writeChooseHeaderStart [none] [some false] [true, false] [false, true] 3) 22 =
      PMF.pure (writeChooseHeaderFinish [none] [some false] [true, false] [false, true] 3) :=
  writeChooseHeader_eval _ _ _ _ _
example : (writeChooseHeaderFinish [] [] [true, false] [true] 3).outputBits =
    [true, true, true, false, false] := by
  rw [writeChooseHeader_output]
  rfl
example (bits tail : List Bool) :
    7 * bits.length + 8 ≤ 4 * (FiniteBitEncoding.delimit bits ++ tail).length + 4 :=
  writeChooseHeader_steps_le bits tail

-- The native header and choose tag have exactly the required frame shape.
-- Appending the payload here is a specification equality only; it is not
-- claimed to be a native copying instruction or the completed assembler.
example (bits : List Bool) :
    (writeChooseHeaderFinish [] [] bits [] 0).outputBits ++ bits = frame (false :: bits) := by
  rw [writeChooseHeader_output]
  simp [frame, List.append_assoc]
example : evalConfigWithin writeChooseHeader (writeChooseHeaderStart [] [] [] [] 0) 8 =
    PMF.pure (writeChooseHeaderFinish [] [] [] [] 0) := writeChooseHeader_eval _ _ _ _ _

-- Relabeling tape operands is a code-construction operation. The fair-bit
-- instruction still has exactly its original distribution on paired tapes.
example (p : Program) (c : Configuration) (steps : Nat) :
    evalConfigWithin p.swapTapes c.swapTapes steps =
      (evalConfigWithin p c steps).map Configuration.swapTapes :=
  evalConfigWithin_swapTapes p c steps
example : Program.swapTapes [Instruction.randomBit .output, .halt] =
    [.randomBit .input, .halt] := rfl
example (p : Program) (c d : Configuration) (steps : Nat)
    (run : RunsFor p c d steps) :
    RunsFor p.swapTapes c.swapTapes d.swapTapes steps := run.swapTapes

-- A prepared choose input may be run on the physical output tape. Source
-- output then goes to guarded fresh input cells after the retained DDH data.
example (source : Program) (input : List Bool)
    (savedInput savedOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (GuardedCompiler.rawCompileOpposite source)
      (GuardedCompiler.packInputStart savedInput savedOutput input).swapTapes
      (GuardedCompiler.rawTraceBudget q input.length) =
      (evalConfigWithin source (GuardedCompiler.preparedSource input) (q input.length)).map
        (fun c => (GuardedCompiler.rawResultFrom source input savedInput savedOutput c).swapTapes) :=
  GuardedCompiler.rawCompileOpposite_configuration_eval _ _ _ _ _ halts

example (source : Program) (input : List Bool)
    (savedInput savedDDH : List (Option Bool)) (c : Configuration) :
    ((GuardedCompiler.rawResultFrom source input savedInput savedDDH c).swapTapes).inputTape.left.drop
      c.outputBits.length = savedDDH :=
  GuardedCompiler.rawCompileOpposite_preserves_saved_data _ _ _ _ _

-- Both passes of choose-field assembly are actual native transitions. The
-- status bit is explicitly erased, while caller prefixes and outer blanks
-- are preserved in the physical result.
example (saved publicBits : List (Option Bool)) (key : List Bool)
    (nextBit : Bool) (tail : List Bool) (blanks : Nat) :
    evalConfigWithin assembleChooseField
      (assembleChooseFieldStart saved publicBits key (nextBit :: tail) blanks)
      (assembleChooseFieldSteps key (nextBit :: tail)) =
      PMF.pure (assembleChooseFieldFinish saved publicBits key (nextBit :: tail) blanks) :=
  assembleChooseField_eval _ _ _ _ _ _

example : (assembleChooseFieldFinish [some true] [some false] [] [false] 8).outputBits =
    [false, true, false, false] := rfl
example : (assembleChooseFieldFinish [some true] [some false] [true, false] [false] 8).outputBits =
    [false, true, true, true, false, false, true, false] := rfl

-- Empty element codes still have delimiters. This checks preparation of an
-- actual DDH input rather than assuming a ready-made choose-call input.
example : prepareDDHChooseCallSteps 0 [] [] [false] = 104 := rfl
example : evalConfigWithin prepareDDHChooseCall
    (Configuration.initial (encodeSecurityParameter 0 ++ frame [] ++
      frame (FiniteBitEncoding.delimit [] ++ FiniteBitEncoding.delimit [] ++ []))) 104 =
    PMF.pure (prepareDDHChooseCallFinish 0 [] [] [false]) := by
  have h := prepareDDHChooseCall_triple_eval 0 [] [] [] []
  exact h

-- A nonempty key, public instance, and trailing element exercise counting,
-- both native copies, restoration, storage reservation, and both head moves.
example : prepareDDHChooseCall.length = 118 := rfl
example : prepareDDHChooseCallSteps 1 [false] [true, false] [false, true] = 228 := rfl
example : evalConfigWithin prepareDDHChooseCall
    (Configuration.initial (encodeSecurityParameter 1 ++ frame [false] ++
      frame (FiniteBitEncoding.delimit [true, false] ++ FiniteBitEncoding.delimit [] ++ [true]))) 228 =
    PMF.pure (prepareDDHChooseCallFinish 1 [false] [true, false] [false, true]) :=
  prepareDDHChooseCall_triple_eval _ _ _ _ _

-- DDH data are restored exactly and saved behind a real blank separator.
example (n : Nat) (instanceBits key tail : List Bool) :
    (prepareDDHChooseCallFinish n instanceBits key tail).inputTape.bits =
      encodeSecurityParameter n ++ frame instanceBits ++ frame (FiniteBitEncoding.delimit key ++ tail) := by
  simp [prepareDDHChooseCallFinish, Tape.bits, List.filterMap_append, List.append_assoc]

-- The source-call fixture retains physical blank padding. Cell equivalence
-- licenses the same bit-machine transitions; no normalization opcode exists.
example (n : Nat) (instanceBits key tail : List Bool) :
    ((prepareDDHChooseCallFinish n instanceBits key tail).resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart [none]
        (none :: (encodeSecurityParameter n ++ frame instanceBits ++
          frame (FiniteBitEncoding.delimit key ++ tail)).reverse.map some ++ [none])
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))).swapTapes :=
  prepareDDHChooseCall_source_layout _ _ _ _

example (n : Nat) (instanceBits key : List Bool) (nextBit : Bool) (tail : List Bool) :
    HaltsWithin prepareDDHChooseCall
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail))
      (60 * (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)).length + 100) :=
  prepareDDHChooseCall_haltsWithin _ _ _ _ _

-- The complete choose stage includes actual input assembly, guarded source
-- execution, return, and final halt. A randomized source is embedded as code.
example : (GuardedCompiler.chooseCompile Machine.Examples.randomOutputBit).length = 412 := by
  exact GuardedCompiler.chooseCompile_length _
example : GuardedCompiler.chooseTraceBudget (fun _ => 2) 0 [] [] [false] = 1243 := rfl
example : HaltsWithin (GuardedCompiler.chooseCompile Machine.Examples.randomOutputBit)
    (encodeSecurityParameter 0 ++ frame [] ++ frame [false, false]) 1243 :=
  GuardedCompiler.chooseCompile_haltsWithin Machine.Examples.randomOutputBit 0 [] [] false [] (fun _ => 2)
    (Machine.Examples.randomOutputBit_haltsWithin_any _)

-- Both fair source outcomes are retained by the actual wrapper. The saved
-- DDH input is present in the observed tape on either branch.
example :
    (evalConfigWithin (GuardedCompiler.chooseCompile Machine.Examples.randomOutputBit)
      (Configuration.initial (encodeSecurityParameter 0 ++ frame [] ++ frame [false, false])) 1243).map
      (fun c => (c.halted, c.inputTape.bits)) =
    (evalConfigWithin Machine.Examples.randomOutputBit
      (GuardedCompiler.preparedSource (encodeSecurityParameter 0 ++ frame [] ++ frame [false])) 2).map
      (fun c => (true, encodeSecurityParameter 0 ++ frame [] ++ frame [false, false] ++ c.outputBits)) :=
  GuardedCompiler.chooseCompile_evalResult Machine.Examples.randomOutputBit 0 [] [] false [] (fun _ => 2)
    (Machine.Examples.randomOutputBit_haltsWithin_any _)

end Foundation.Examples.ProtocolPreparation
