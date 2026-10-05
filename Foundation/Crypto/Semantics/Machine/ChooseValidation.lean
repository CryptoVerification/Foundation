import Foundation.Crypto.Semantics.Machine.ChooseCheckContinuation
import Foundation.Crypto.Semantics.Machine.ChooseSavedCheck
import Foundation.Crypto.Semantics.Machine.FramedChooseFirstPower
import Foundation.Crypto.Semantics.Machine.FramedChooseSecondPower
import Foundation.Crypto.Semantics.Machine.ChooseAcceptedOutput
import Foundation.Crypto.Semantics.Machine.FramedChooseDefaultOutput

namespace Machine.ChooseValidation

set_option maxRecDepth 4096

/-- The second subgroup decision is followed by physical request recovery
and either complete response copying or the generator fallback. -/
def afterFirstPower : Program :=
  ChooseCheckContinuation.withCheck FramedChooseSecondPower.program
    ChooseAcceptedOutput.program FramedChooseDefaultOutput.program

/-- Check the first candidate's subgroup condition before the second one.
A failed check goes directly to the same generator fallback. -/
def afterRanges : Program :=
  ChooseCheckContinuation.withCheck FramedChooseFirstPower.program
    afterFirstPower FramedChooseDefaultOutput.program

/-- The range decision uses the physically saved original request, and
both successful ranges are required before invoking subgroup arithmetic. -/
def afterWidths : Program :=
  ChooseCheckContinuation.withCheck ChooseSavedCheck.program
    afterRanges FramedChooseDefaultOutput.program

/-- One connected finite choose-validation body: widths, both ranges, and
both subgroup decisions, with actual request recovery between the stages.
Only the success branch copies the original reply, including its state.

This body is not yet a `RepresentedChooseNormalizer` witness. Semantic
correctness for arbitrary replies on represented instance requests is proved
in `PrimeOrderChooseValidation`. `ChooseSafeValidation` supplies the outer
frame guard, and `ChooseValidationRuntime` charges the full connected trace
at a common polynomial budget. -/
def program : Program :=
  ChooseCheckContinuation.withCheck
    (ChooseSavedCheck.withCore ChooseWidthDecision.program)
    afterWidths FramedChooseDefaultOutput.program

/-- All validation decisions are deterministic native instructions. -/
theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  have hSecond := ChooseCheckContinuation.withCheck_no_randomBit
    FramedChooseSecondPower.program ChooseAcceptedOutput.program FramedChooseDefaultOutput.program
    FramedChooseSecondPower.no_randomBit ChooseAcceptedOutput.no_randomBit
    FramedChooseDefaultOutput.no_randomBit
  have hFirst := ChooseCheckContinuation.withCheck_no_randomBit
    FramedChooseFirstPower.program afterFirstPower FramedChooseDefaultOutput.program
    FramedChooseFirstPower.no_randomBit hSecond FramedChooseDefaultOutput.no_randomBit
  have hRange := ChooseCheckContinuation.withCheck_no_randomBit
    ChooseSavedCheck.program afterRanges FramedChooseDefaultOutput.program
    (ChooseSavedCheck.withCore_no_randomBit ChooseRangeDecision.program ChooseRangeDecision.no_randomBit)
    hFirst FramedChooseDefaultOutput.no_randomBit
  exact ChooseCheckContinuation.withCheck_no_randomBit
    (ChooseSavedCheck.withCore ChooseWidthDecision.program) afterWidths FramedChooseDefaultOutput.program
    (ChooseSavedCheck.withCore_no_randomBit ChooseWidthDecision.program ChooseWidthDecision.no_randomBit)
    hRange FramedChooseDefaultOutput.no_randomBit tape

/-- The connected second subgroup gate returns the entire original reply
on success and the represented generator pair on failure. Arbitrary state
bits remain part of the actual copied request. -/
theorem runs_afterFirstPower (n modulus exponent generator firstCandidate candidate : Nat)
    (hOne : 1 < modulus) (hCandidate : candidate < modulus)
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (state : List Bool) :
    let width := n+3
    let generatorBits := Binary.encode width generator
    let instanceBits := Binary.encode width modulus ++ Binary.encode width exponent ++ generatorBits
    let reply := canonicalMessageBits (Binary.encode width firstCandidate)
      (Binary.encode width candidate) state
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let status := BinaryIsOneInPlace.accepts (Binary.encode width (candidate ^ exponent % modulus))
    ∃ target used,
      RunsFor afterFirstPower (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits =
        (if status then reply else canonicalMessageBits generatorBits generatorBits []) := by
  dsimp only
  let generatorBits := Binary.encode (n+3) generator
  let instanceBits := Binary.encode (n+3) modulus ++ Binary.encode (n+3) exponent ++ generatorBits
  let reply := canonicalMessageBits (Binary.encode (n+3) firstCandidate)
    (Binary.encode (n+3) candidate) state
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let status := BinaryIsOneInPlace.accepts (Binary.encode (n+3) (candidate ^ exponent % modulus))
  obtain ⟨c, checked, checkUsed, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    FramedChooseSecondPower.runs_numbers n modulus exponent generator firstCandidate candidate
      hOne hCandidate hExponent hModulus state
  have hNext : ∃ next nextUsed,
      RunsFor (if status then ChooseAcceptedOutput.program else FramedChooseDefaultOutput.program)
        (Configuration.initial request) next nextUsed ∧ next.halted = true ∧
      next.outputBits = (if status then reply else canonicalMessageBits generatorBits generatorBits []) := by
    cases hStatus : status with
    | false =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          FramedChooseDefaultOutput.runs_valid n (Binary.encode (n+3) modulus)
            (Binary.encode (n+3) exponent) generatorBits reply (by simp) (by simp) (by simp [generatorBits])
        exact ⟨next, used, by simpa [hStatus, request, instanceBits] using run,
          hHalt, by simpa [hStatus] using hOutput⟩
    | true =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ := ChooseAcceptedOutput.runs_valid n instanceBits reply
        exact ⟨next, used, by simpa [hStatus, request] using run,
          hHalt, by simpa [hStatus] using hOutput⟩
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ := hNext
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck FramedChooseSecondPower.program
      BinaryPowerIsOne.program
      (BinaryColumnSlotFill.fullSlots (Binary.encode (n+3) candidate)
        (Binary.encode (n+3) exponent) (Binary.encode (n+3) modulus))
      request c status hBits checked checkUsed
      (by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
        List.append_assoc, List.cons_append] using checkRun) checkHalt
      ⟨rfl, rfl,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.1,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.2⟩
      ChooseAcceptedOutput.program FramedChooseDefaultOutput.program
      next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- Both actual subgroup computations are connected by native request
recovery. Success preserves the complete reply, including arbitrary state;
either failed subgroup decision uses the same generator fallback. -/
theorem runs_afterRanges (n modulus exponent generator firstCandidate secondCandidate : Nat)
    (hOne : 1 < modulus) (hFirst : firstCandidate < modulus)
    (hSecond : secondCandidate < modulus)
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (state : List Bool) :
    let width := n+3
    let generatorBits := Binary.encode width generator
    let instanceBits := Binary.encode width modulus ++ Binary.encode width exponent ++ generatorBits
    let reply := canonicalMessageBits (Binary.encode width firstCandidate)
      (Binary.encode width secondCandidate) state
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let firstStatus := BinaryIsOneInPlace.accepts (Binary.encode width (firstCandidate ^ exponent % modulus))
    let secondStatus := BinaryIsOneInPlace.accepts (Binary.encode width (secondCandidate ^ exponent % modulus))
    ∃ target used,
      RunsFor afterRanges (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits =
        (if firstStatus && secondStatus then reply else canonicalMessageBits generatorBits generatorBits []) := by
  dsimp only
  let generatorBits := Binary.encode (n+3) generator
  let instanceBits := Binary.encode (n+3) modulus ++ Binary.encode (n+3) exponent ++ generatorBits
  let reply := canonicalMessageBits (Binary.encode (n+3) firstCandidate)
    (Binary.encode (n+3) secondCandidate) state
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let firstStatus := BinaryIsOneInPlace.accepts (Binary.encode (n+3) (firstCandidate ^ exponent % modulus))
  let secondStatus := BinaryIsOneInPlace.accepts (Binary.encode (n+3) (secondCandidate ^ exponent % modulus))
  obtain ⟨c, checked, checkUsed, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    FramedChooseFirstPower.runs_numbers n modulus exponent generator firstCandidate
      hOne hFirst hExponent hModulus (FiniteBitEncoding.delimit (Binary.encode (n+3) secondCandidate) ++ state)
  have hNext : ∃ next nextUsed,
      RunsFor (if firstStatus then afterFirstPower else FramedChooseDefaultOutput.program)
        (Configuration.initial request) next nextUsed ∧ next.halted = true ∧
      next.outputBits = (if firstStatus && secondStatus then reply
        else canonicalMessageBits generatorBits generatorBits []) := by
    cases hStatus : firstStatus with
    | false =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          FramedChooseDefaultOutput.runs_valid n (Binary.encode (n+3) modulus)
            (Binary.encode (n+3) exponent) generatorBits reply (by simp) (by simp) (by simp [generatorBits])
        exact ⟨next, used, by simpa [hStatus, request, instanceBits] using run,
          hHalt, by simpa [hStatus] using hOutput⟩
    | true =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          runs_afterFirstPower n modulus exponent generator firstCandidate secondCandidate
            hOne hSecond hExponent hModulus state
        exact ⟨next, used, by simpa [hStatus, request, instanceBits, reply, generatorBits] using run,
          hHalt, by simpa [hStatus, secondStatus, reply, generatorBits] using hOutput⟩
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ := hNext
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck FramedChooseFirstPower.program
      BinaryPowerIsOne.program
      (BinaryColumnSlotFill.fullSlots (Binary.encode (n+3) firstCandidate)
        (Binary.encode (n+3) exponent) (Binary.encode (n+3) modulus))
      request c firstStatus hBits checked checkUsed
      (by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
        List.append_assoc, List.cons_append] using checkRun) checkHalt
      ⟨rfl, rfl,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.1,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.2⟩
      afterFirstPower FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- The connected range gate rejects either out-of-range candidate before
subgroup arithmetic. Every fixed-width candidate and arbitrary trailing
state is admitted to this operational statement. -/
theorem runs_afterWidths (n modulus exponent generator firstCandidate secondCandidate : Nat)
    (hOne : 1 < modulus)
    (hFirstWidth : firstCandidate < 2 ^ (n+3))
    (hSecondWidth : secondCandidate < 2 ^ (n+3))
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (state : List Bool) :
    let width := n+3
    let generatorBits := Binary.encode width generator
    let instanceBits := Binary.encode width modulus ++ Binary.encode width exponent ++ generatorBits
    let reply := canonicalMessageBits (Binary.encode width firstCandidate)
      (Binary.encode width secondCandidate) state
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let ranges := decide (firstCandidate < modulus ∧ secondCandidate < modulus)
    let firstStatus := BinaryIsOneInPlace.accepts (Binary.encode width (firstCandidate ^ exponent % modulus))
    let secondStatus := BinaryIsOneInPlace.accepts (Binary.encode width (secondCandidate ^ exponent % modulus))
    ∃ target used,
      RunsFor afterWidths (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits =
        (if ranges && (firstStatus && secondStatus) then reply
          else canonicalMessageBits generatorBits generatorBits []) := by
  dsimp only
  let generatorBits := Binary.encode (n+3) generator
  let instanceBits := Binary.encode (n+3) modulus ++ Binary.encode (n+3) exponent ++ generatorBits
  let reply := canonicalMessageBits (Binary.encode (n+3) firstCandidate)
    (Binary.encode (n+3) secondCandidate) state
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let ranges := decide (firstCandidate < modulus ∧ secondCandidate < modulus)
  let firstStatus := BinaryIsOneInPlace.accepts (Binary.encode (n+3) (firstCandidate ^ exponent % modulus))
  let secondStatus := BinaryIsOneInPlace.accepts (Binary.encode (n+3) (secondCandidate ^ exponent % modulus))
  obtain ⟨c, checked, checkUsed, _, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_ranges n (n+3) (Binary.encode (n+3) modulus)
      (Binary.encode (n+3) exponent ++ generatorBits)
      (Binary.encode (n+3) firstCandidate) (Binary.encode (n+3) secondCandidate) state
      (by omega) (by simp) (by simp [generatorBits]; omega) (by simp) (by simp)
  have hRangeBits : c.outputBits = [ranges] := by
    simpa only [Binary.value_encode hFirstWidth, Binary.value_encode hSecondWidth,
      Binary.value_encode hModulus] using hBits
  have hNext : ∃ next nextUsed,
      RunsFor (if ranges then afterRanges else FramedChooseDefaultOutput.program)
        (Configuration.initial request) next nextUsed ∧ next.halted = true ∧
      next.outputBits = (if ranges && (firstStatus && secondStatus) then reply
        else canonicalMessageBits generatorBits generatorBits []) := by
    cases hStatus : ranges with
    | false =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          FramedChooseDefaultOutput.runs_valid n (Binary.encode (n+3) modulus)
            (Binary.encode (n+3) exponent) generatorBits reply (by simp) (by simp) (by simp [generatorBits])
        exact ⟨next, used, by simpa [hStatus, request, instanceBits] using run,
          hHalt, by simpa [hStatus] using hOutput⟩
    | true =>
        have hRanges : firstCandidate < modulus ∧ secondCandidate < modulus := by
          simpa only [ranges, decide_eq_true_eq] using hStatus
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          runs_afterRanges n modulus exponent generator firstCandidate secondCandidate
            hOne hRanges.1 hRanges.2 hExponent hModulus state
        exact ⟨next, used, by simpa [hStatus, request, instanceBits, reply, generatorBits] using run,
          hHalt, by simpa [hStatus, firstStatus, secondStatus, reply, generatorBits] using hOutput⟩
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ := hNext
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck ChooseSavedCheck.program
      ChooseRangeDecision.program request request c ranges hRangeBits checked checkUsed
      (by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
        List.append_assoc, List.cons_append] using checkRun) checkHalt
      ⟨rfl, rfl,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.1,
        by simpa only [request, instanceBits, generatorBits, reply, canonicalMessageBits,
          List.append_assoc, List.cons_append, Configuration.resumeAt] using hReturned.2.2.2⟩
      afterRanges FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- Complete four-stage operational validation for two complete fixed-width
candidate fields. Out-of-range and failed subgroup decisions return the
native fallback; all successful decisions preserve every state bit. -/
theorem runs_numbers (n modulus exponent generator firstCandidate secondCandidate : Nat)
    (hOne : 1 < modulus)
    (hFirstWidth : firstCandidate < 2 ^ (n+3))
    (hSecondWidth : secondCandidate < 2 ^ (n+3))
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (state : List Bool) :
    let width := n+3
    let generatorBits := Binary.encode width generator
    let instanceBits := Binary.encode width modulus ++ Binary.encode width exponent ++ generatorBits
    let reply := canonicalMessageBits (Binary.encode width firstCandidate)
      (Binary.encode width secondCandidate) state
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let ranges := decide (firstCandidate < modulus ∧ secondCandidate < modulus)
    let firstStatus := BinaryIsOneInPlace.accepts (Binary.encode width (firstCandidate ^ exponent % modulus))
    let secondStatus := BinaryIsOneInPlace.accepts (Binary.encode width (secondCandidate ^ exponent % modulus))
    ∃ target used,
      RunsFor program (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits =
        (if ranges && (firstStatus && secondStatus) then reply
          else canonicalMessageBits generatorBits generatorBits []) := by
  dsimp only
  let generatorBits := Binary.encode (n+3) generator
  let instanceBits := Binary.encode (n+3) modulus ++ Binary.encode (n+3) exponent ++ generatorBits
  let payload := FiniteBitEncoding.delimit (Binary.encode (n+3) firstCandidate) ++
    FiniteBitEncoding.delimit (Binary.encode (n+3) secondCandidate) ++ state
  let reply := false :: payload
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  have hLength : instanceBits.length = 3 * (n+3) := by
    simp [instanceBits, generatorBits]; omega
  obtain ⟨c, checked, checkUsed, _, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_widths n (n+3) instanceBits payload hLength
  have hWidthBits : c.outputBits = [true] := by
    simpa [payload, List.append_assoc] using hBits
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ :=
    runs_afterWidths n modulus exponent generator firstCandidate secondCandidate
      hOne hFirstWidth hSecondWidth hExponent hModulus state
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck (ChooseSavedCheck.withCore ChooseWidthDecision.program)
      ChooseWidthDecision.program request request c true hWidthBits checked checkUsed
      checkRun checkHalt ⟨rfl, rfl, hReturned.2.2.1, hReturned.2.2.2⟩
      afterWidths FramedChooseDefaultOutput.program next nextUsed
      (by simpa only [Bool.true_eq, ↓reduceIte, request, instanceBits, generatorBits,
        reply, payload, canonicalMessageBits] using nextRun) nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- Malformed or incorrectly sized raw candidate fields are rejected by
actual width-check execution before range or subgroup arithmetic is called.
The payload may be any finite bitstring, with no canonicality assumption. -/
theorem runs_rejected_widths (n : Nat) (modulus exponent generator payload : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (hReject : (FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = n+3) &&
        (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = n+3))) = false) :
    ∃ target used,
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++
          frame (modulus ++ exponent ++ generator) ++ frame (false :: payload))) target used ∧
      target.halted = true ∧ target.outputBits = canonicalMessageBits generator generator [] := by
  let instanceBits := modulus ++ exponent ++ generator
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: payload)
  have hLength : instanceBits.length = 3 * (n+3) := by
    simp only [instanceBits, List.length_append]; omega
  obtain ⟨c, checked, checkUsed, _, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_widths n (n+3) instanceBits payload hLength
  have hStatus : c.outputBits = [false] := by simpa only [hReject] using hBits
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ :=
    FramedChooseDefaultOutput.runs_valid n modulus exponent generator (false :: payload)
      hModulus hExponent hGenerator
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck (ChooseSavedCheck.withCore ChooseWidthDecision.program)
      ChooseWidthDecision.program request request c false hStatus checked checkUsed
      checkRun checkHalt ⟨rfl, rfl, hReturned.2.2.1, hReturned.2.2.2⟩
      afterWidths FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- The complete validation body also handles empty and wrong-stage replies.
Its native width gate rejects them and restores the actual request before
extracting the represented generator fallback. -/
theorem runs_wrong_tag (n : Nat) (modulus exponent generator reply : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (hTag : (Tape.ofBits reply).current = none ∨ (Tape.ofBits reply).current = some true) :
    ∃ target used,
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++
          frame (modulus ++ exponent ++ generator) ++ frame reply)) target used ∧
      target.halted = true ∧ target.outputBits = canonicalMessageBits generator generator [] := by
  let instanceBits := modulus ++ exponent ++ generator
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨c, checked, checkUsed, _, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_widths_wrong_tag n instanceBits reply hTag
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ :=
    FramedChooseDefaultOutput.runs_valid n modulus exponent generator reply
      hModulus hExponent hGenerator
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    ChooseCheckContinuation.runs_withCheck (ChooseSavedCheck.withCore ChooseWidthDecision.program)
      ChooseWidthDecision.program request request c false hBits checked checkUsed
      checkRun checkHalt ⟨rfl, rfl, hReturned.2.2.1, hReturned.2.2.2⟩
      afterWidths FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

/-- Numeric reconstruction is used only to state the result of native
execution. The original fixed-width fields, including redundant leading
zeroes, remain the actual input to the connected validation code. -/
theorem runs_fields (n modulus exponent generator : Nat)
    (hOne : 1 < modulus)
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (first second state : List Bool)
    (hFirst : first.length = n+3) (hSecond : second.length = n+3) :
    let generatorBits := Binary.encode (n+3) generator
    let instanceBits := Binary.encode (n+3) modulus ++ Binary.encode (n+3) exponent ++ generatorBits
    let reply := canonicalMessageBits first second state
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let ranges := decide (Binary.value first < modulus ∧ Binary.value second < modulus)
    let firstStatus := BinaryIsOneInPlace.accepts
      (Binary.encode (n+3) (Binary.value first ^ exponent % modulus))
    let secondStatus := BinaryIsOneInPlace.accepts
      (Binary.encode (n+3) (Binary.value second ^ exponent % modulus))
    ∃ target used,
      RunsFor program (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits =
        (if ranges && (firstStatus && secondStatus) then reply
          else canonicalMessageBits generatorBits generatorBits []) := by
  have hEncodeFirst : Binary.encode (n+3) (Binary.value first) = first := by
    simpa only [hFirst] using Binary.encode_value first
  have hEncodeSecond : Binary.encode (n+3) (Binary.value second) = second := by
    simpa only [hSecond] using Binary.encode_value second
  simpa only [hEncodeFirst, hEncodeSecond] using
    runs_numbers n modulus exponent generator (Binary.value first) (Binary.value second)
      hOne (by simpa only [hFirst] using Binary.value_lt first)
      (by simpa only [hSecond] using Binary.value_lt second) hExponent hModulus state

end Machine.ChooseValidation
