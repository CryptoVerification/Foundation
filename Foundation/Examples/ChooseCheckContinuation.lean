import Foundation.Machine.ChooseCheckContinuation
import Foundation.Machine.ChooseSavedCheck
import Foundation.Machine.ChooseAcceptedOutput
import Foundation.Machine.FramedChooseDefaultOutput

namespace Examples.ChooseCheckContinuation

/-- A connected operational test: save the framed request, check both raw
field widths, read the returned bit, physically recover the saved request,
and either copy the entire reply or emit the generator fallback. This tests
only the width gate; range and subgroup gates are still needed by the final
normalizer. The adversary state in `payload` is never reconstructed. -/
example (n : Nat) (modulus exponent generator payload : List Bool)
    (hModulus : modulus.length = n + 3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let instanceBits := modulus ++ exponent ++ generator
    let reply := false :: payload
    let raw := Machine.encodeSecurityParameter n ++ Machine.frame instanceBits ++ Machine.frame reply
    let decision := (Machine.FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = n + 3) &&
        (Machine.FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = n + 3)))
    ∃ target used,
      Machine.RunsFor (Machine.ChooseCheckContinuation.withCheck
        (Machine.ChooseSavedCheck.withCore Machine.ChooseWidthDecision.program)
        Machine.ChooseAcceptedOutput.program Machine.FramedChooseDefaultOutput.program)
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧ target.outputBits =
        (if decision then reply else Machine.canonicalMessageBits generator generator []) := by
  dsimp only
  let instanceBits := modulus ++ exponent ++ generator
  let reply := false :: payload
  let raw := Machine.encodeSecurityParameter n ++ Machine.frame instanceBits ++ Machine.frame reply
  let decision := (Machine.FiniteBitEncoding.undelimit payload).any (fun pair =>
    decide (pair.1.length = n + 3) &&
      (Machine.FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = n + 3)))
  have hLength : instanceBits.length = 3 * (n + 3) := by
    simp only [instanceBits, List.length_append]
    omega
  obtain ⟨c, checked, checkUsed, _, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    Machine.ChooseSavedCheck.runs_widths n (n + 3) instanceBits payload hLength
  have hNext : ∃ next nextUsed,
      Machine.RunsFor (if decision then Machine.ChooseAcceptedOutput.program
        else Machine.FramedChooseDefaultOutput.program)
        (Machine.Configuration.initial raw) next nextUsed ∧ next.halted = true ∧
      next.outputBits = (if decision then reply else Machine.canonicalMessageBits generator generator []) := by
    cases hDecision : decision with
    | false =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          Machine.FramedChooseDefaultOutput.runs_valid n modulus exponent generator reply
            hModulus hExponent hGenerator
        refine ⟨next, used, ?_, hHalt, ?_⟩
        · simpa [hDecision, raw, instanceBits] using run
        · simpa [hDecision] using hOutput
    | true =>
        obtain ⟨next, used, run, hHalt, hOutput⟩ :=
          Machine.ChooseAcceptedOutput.runs_valid n instanceBits reply
        refine ⟨next, used, ?_, hHalt, ?_⟩
        · simpa [hDecision, raw] using run
        · simpa [hDecision] using hOutput
  obtain ⟨next, nextUsed, nextRun, nextHalt, nextBits⟩ := hNext
  obtain ⟨target, used, _, run, hHalt, hOutput⟩ :=
    Machine.ChooseCheckContinuation.runs_withCheck
      (Machine.ChooseSavedCheck.withCore Machine.ChooseWidthDecision.program)
      Machine.ChooseWidthDecision.program raw raw c decision hBits checked checkUsed
      checkRun checkHalt ⟨rfl, rfl, hReturned.2.2.1, hReturned.2.2.2⟩
      Machine.ChooseAcceptedOutput.program Machine.FramedChooseDefaultOutput.program
      next nextUsed nextRun nextHalt
  exact ⟨target, used, run, hHalt, hOutput.trans nextBits⟩

end Examples.ChooseCheckContinuation
