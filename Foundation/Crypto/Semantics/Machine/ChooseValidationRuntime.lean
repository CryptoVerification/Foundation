import Foundation.Crypto.Semantics.Machine.ChooseValidation

namespace Machine.ChooseValidationRuntime

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Includes the actual fallback copy on every failure branch. -/
def outputBudget (L : Nat) : Nat := 10000000010000 * (L+1)
def secondBudget (L : Nat) : Nat :=
  5 * FramedChooseSecondPower.budget L + 6*L + outputBudget L + 40
def firstBudget (L : Nat) : Nat :=
  5 * FramedChooseFirstPower.budget L + 6*L + secondBudget L + outputBudget L + 40
def rangeBudget (L : Nat) : Nat :=
  5 * ChooseSavedCheck.budget ChooseRangeDecision.budget L + 6*L +
    firstBudget L + outputBudget L + 40

theorem runs_second (n : Nat) (p q g a b state : List Bool)
    (hp : p.length = n+3) (hq : q.length = p.length)
    (hg : g.length = p.length) (ha : a.length = p.length) (hb : b.length = p.length) :
    let raw := encodeSecurityParameter n ++ frame (p++q++g) ++
      frame (canonicalMessageBits a b state)
    ∃ target used, used ≤ secondBudget raw.length ∧
      RunsFor ChooseValidation.afterFirstPower (Configuration.initial raw) target used ∧
      target.halted = true := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (p++q++g) ++ frame (canonicalMessageBits a b state)
  obtain ⟨c, checked, checkUsed, status, hUsed, checkRun, checkHalt, hBits, hReturned⟩ :=
    FramedChooseSecondPower.runs_fields_decision_bounded n p q g a b state hp hq hg hb
  have hCheck : RunsFor FramedChooseSecondPower.program (Configuration.initial raw) checked checkUsed := by
    simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using checkRun
  have hNext : ∃ next nextUsed, nextUsed ≤ outputBudget raw.length ∧
      RunsFor (if status then ChooseAcceptedOutput.program else FramedChooseDefaultOutput.program)
        (Configuration.initial raw) next nextUsed ∧ next.halted = true := by
    cases hStatus : status with
    | false =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := FramedChooseDefaultOutput.runs_any raw
      exact ⟨next, used, by
          have hb : used ≤ outputBudget raw.length := by
            change used ≤ 10000000010000*(raw.length+1)
            omega
          omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
    | true =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := ChooseAcceptedOutput.runs_any raw
      exact ⟨next, used, by
          have hb : used ≤ outputBudget raw.length := by
            change used ≤ 10000000010000*(raw.length+1)
            omega
          omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
  obtain ⟨next, nextUsed, hNextUsed, nextRun, nextHalt⟩ := hNext
  obtain ⟨target, used, hu, run, hHalt, _⟩ :=
    ChooseCheckContinuation.runs_withCheck_bounded FramedChooseSecondPower.program
      BinaryPowerIsOne.program (BinaryColumnSlotFill.fullSlots b q p) raw
      c status hBits checked checkUsed hCheck checkHalt
      (by simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using hReturned)
      ChooseAcceptedOutput.program FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  refine ⟨target, used, ?_, run, hHalt⟩
  change checkUsed ≤ FramedChooseSecondPower.budget raw.length at hUsed
  change used ≤ secondBudget raw.length
  unfold secondBudget
  omega

theorem runs_first (n : Nat) (p q g a b state : List Bool)
    (hp : p.length = n+3) (hq : q.length = p.length)
    (hg : g.length = p.length) (ha : a.length = p.length) (hb : b.length = p.length) :
    let raw := encodeSecurityParameter n ++ frame (p++q++g) ++
      frame (canonicalMessageBits a b state)
    ∃ target used, used ≤ firstBudget raw.length ∧
      RunsFor ChooseValidation.afterRanges (Configuration.initial raw) target used ∧
      target.halted = true := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (p++q++g) ++ frame (canonicalMessageBits a b state)
  obtain ⟨c, checked, checkUsed, status, hUsed, checkRun, checkHalt, hBits, hReturned⟩ :=
    FramedChooseFirstPower.runs_fields_decision_bounded n p q g a
      (FiniteBitEncoding.delimit b ++ state) hp hq hg ha
  have hCheck : RunsFor FramedChooseFirstPower.program (Configuration.initial raw) checked checkUsed := by
    simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using checkRun
  have hNext : ∃ next nextUsed, nextUsed ≤ secondBudget raw.length + outputBudget raw.length ∧
      RunsFor (if status then ChooseValidation.afterFirstPower else FramedChooseDefaultOutput.program)
        (Configuration.initial raw) next nextUsed ∧ next.halted = true := by
    cases hStatus : status with
    | false =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := FramedChooseDefaultOutput.runs_any raw
      exact ⟨next, used, by
          have hb : used ≤ outputBudget raw.length := by
            change used ≤ 10000000010000*(raw.length+1)
            omega
          omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
    | true =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := runs_second n p q g a b state hp hq hg ha hb
      exact ⟨next, used, by change used ≤ secondBudget raw.length at hUsed; omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
  obtain ⟨next, nextUsed, hNextUsed, nextRun, nextHalt⟩ := hNext
  obtain ⟨target, used, hu, run, hHalt, _⟩ :=
    ChooseCheckContinuation.runs_withCheck_bounded FramedChooseFirstPower.program
      BinaryPowerIsOne.program (BinaryColumnSlotFill.fullSlots a q p) raw
      c status hBits checked checkUsed hCheck checkHalt
      (by simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using hReturned)
      ChooseValidation.afterFirstPower FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  refine ⟨target, used, ?_, run, hHalt⟩
  have hCheckUsed : checkUsed ≤ FramedChooseFirstPower.budget raw.length := by
    simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using hUsed
  change used ≤ firstBudget raw.length
  unfold firstBudget
  omega

theorem runs_ranges (n : Nat) (p q g a b state : List Bool)
    (hp : p.length = n+3) (hq : q.length = p.length)
    (hg : g.length = p.length) (ha : a.length = p.length) (hb : b.length = p.length) :
    let raw := encodeSecurityParameter n ++ frame (p++q++g) ++
      frame (canonicalMessageBits a b state)
    ∃ target used, used ≤ rangeBudget raw.length ∧
      RunsFor ChooseValidation.afterWidths (Configuration.initial raw) target used ∧
      target.halted = true := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (p++q++g) ++ frame (canonicalMessageBits a b state)
  let status := decide (Binary.value a < Binary.value p ∧ Binary.value b < Binary.value p)
  obtain ⟨c, checked, checkUsed, hUsed, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_ranges n (n+3) p (q++g) a b state
      (by omega) hp (by simp only [List.length_append]; omega)
      (ha.trans hp) (hb.trans hp)
  have hCheck : RunsFor ChooseSavedCheck.program (Configuration.initial raw) checked checkUsed := by
    simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append] using checkRun
  have hNext : ∃ next nextUsed, nextUsed ≤ firstBudget raw.length + outputBudget raw.length ∧
      RunsFor (if status then ChooseValidation.afterRanges else FramedChooseDefaultOutput.program)
        (Configuration.initial raw) next nextUsed ∧ next.halted = true := by
    cases hStatus : status with
    | false =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := FramedChooseDefaultOutput.runs_any raw
      exact ⟨next, used, by
          have hb : used ≤ outputBudget raw.length := by
            change used ≤ 10000000010000*(raw.length+1)
            omega
          omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
    | true =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := runs_first n p q g a b state hp hq hg ha hb
      exact ⟨next, used, by change used ≤ firstBudget raw.length at hUsed; omega, by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
  obtain ⟨next, nextUsed, hNextUsed, nextRun, nextHalt⟩ := hNext
  obtain ⟨target, used, hu, run, hHalt, _⟩ :=
    ChooseCheckContinuation.runs_withCheck_bounded ChooseSavedCheck.program
      ChooseRangeDecision.program raw raw c status hBits checked checkUsed hCheck checkHalt
      ⟨rfl, rfl,
        by simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append,
          Configuration.resumeAt] using hReturned.2.2.1,
        by simpa only [raw, canonicalMessageBits, List.append_assoc, List.cons_append,
          Configuration.resumeAt] using hReturned.2.2.2⟩
      ChooseValidation.afterRanges FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  refine ⟨target, used, ?_, run, hHalt⟩
  have hCheckUsed : checkUsed ≤ ChooseSavedCheck.budget ChooseRangeDecision.budget raw.length := by
    simpa only [ChooseSavedCheck.budget, raw, canonicalMessageBits, List.append_assoc, List.cons_append] using hUsed
  change used ≤ rangeBudget raw.length
  unfold rangeBudget
  omega

/-- The bound is independent of the numeric meaning of the instance fields. -/
def budget (L : Nat) : Nat :=
  5 * ChooseSavedCheck.budget ChooseWidthDecision.budget L + 6*L +
    rangeBudget L + outputBudget L + 40

private def widthStatus (width : Nat) (reply : List Bool) : Bool :=
  match reply with
  | false :: payload => (FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = width) &&
        (FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = width)))
  | _ => false

theorem runs_fields (n : Nat) (p q g reply : List Bool)
    (hp : p.length = n+3) (hq : q.length = p.length) (hg : g.length = p.length) :
    let raw := encodeSecurityParameter n ++ frame (p++q++g) ++ frame reply
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor ChooseValidation.program (Configuration.initial raw) target used ∧
      target.halted = true := by
  dsimp only
  let instanceBits := p++q++g
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let status := widthStatus (n+3) reply
  have hLength : instanceBits.length = 3*(n+3) := by
    simp only [instanceBits, List.length_append]; omega
  have hCorrect : evalWithin ChooseWidthDecision.program raw
      (ChooseWidthDecision.budget raw.length) = PMF.pure (some [status]) := by
    cases reply with
    | nil => exact ChooseWidthDecision.eval_wrong_tag n instanceBits [] (Or.inl rfl)
    | cons tag payload =>
      cases tag with
      | true => exact ChooseWidthDecision.eval_wrong_tag n instanceBits (true::payload) (Or.inr rfl)
      | false => exact ChooseWidthDecision.eval_raw_decision n (n+3) instanceBits payload hLength
  obtain ⟨c, checked, checkUsed, hUsed, checkRun, checkHalt, _, hBits, hReturned⟩ :=
    ChooseSavedCheck.runs_request_withCore ChooseWidthDecision.program ChooseWidthDecision.budget
      ChooseWidthDecision.no_randomBit raw [status] (ChooseWidthDecision.haltsWithin raw) hCorrect
  have hNext : ∃ next nextUsed, nextUsed ≤ rangeBudget raw.length + outputBudget raw.length ∧
      RunsFor (if status then ChooseValidation.afterWidths else FramedChooseDefaultOutput.program)
        (Configuration.initial raw) next nextUsed ∧ next.halted = true := by
    cases hStatus : status with
    | false =>
      obtain ⟨next, used, hUsed, run, hHalt⟩ := FramedChooseDefaultOutput.runs_any raw
      exact ⟨next, used, by
          have hb : used ≤ outputBudget raw.length := by
            change used ≤ 10000000010000*(raw.length+1)
            omega
          omega,
        by simpa only [hStatus, Bool.false_eq_true, ↓reduceIte] using run, hHalt⟩
    | true =>
      have hAccept : widthStatus (n+3) reply = true := hStatus
      cases reply with
      | nil => simp [widthStatus] at hAccept
      | cons tag payload =>
        cases tag with
        | true => simp [widthStatus] at hAccept
        | false =>
          cases hFirst : FiniteBitEncoding.undelimit payload with
          | none => simp [widthStatus, hFirst] at hAccept
          | some pair =>
            rcases pair with ⟨a, rest⟩
            cases hSecond : FiniteBitEncoding.undelimit rest with
            | none => simp [widthStatus, hFirst, hSecond] at hAccept
            | some pair =>
              rcases pair with ⟨b, state⟩
              have hLengths : a.length = n+3 ∧ b.length = n+3 := by
                simpa [widthStatus, hFirst, hSecond] using hAccept
              have hLayout : canonicalMessageBits a b state = false :: payload := by
                simp only [canonicalMessageBits, List.cons.injEq, true_and]
                rw [List.append_assoc, FiniteBitEncoding.delimit_append_of_undelimit hSecond]
                exact FiniteBitEncoding.delimit_append_of_undelimit hFirst
              obtain ⟨next, used, hUsed, run, hHalt⟩ :=
                runs_ranges n p q g a b state hp hq hg
                  (hLengths.1.trans hp.symm) (hLengths.2.trans hp.symm)
              have hRun : RunsFor ChooseValidation.afterWidths
                  (Configuration.initial raw) next used := by
                simpa only [raw, instanceBits, hLayout] using run
              have hBound : used ≤ rangeBudget raw.length := by
                simpa only [raw, instanceBits, hLayout] using hUsed
              exact ⟨next, used, by omega,
                by simpa only [hStatus, ↓reduceIte] using hRun, hHalt⟩
  obtain ⟨next, nextUsed, hNextUsed, nextRun, nextHalt⟩ := hNext
  obtain ⟨target, used, hu, run, hHalt, _⟩ :=
    ChooseCheckContinuation.runs_withCheck_bounded
      (ChooseSavedCheck.withCore ChooseWidthDecision.program)
      ChooseWidthDecision.program raw raw c status hBits checked checkUsed checkRun checkHalt
      ⟨rfl, rfl, hReturned.2.2.1, hReturned.2.2.2⟩
      ChooseValidation.afterWidths FramedChooseDefaultOutput.program next nextUsed nextRun nextHalt
  refine ⟨target, used, ?_, run, hHalt⟩
  change used ≤ budget raw.length
  change checkUsed ≤ ChooseSavedCheck.budget ChooseWidthDecision.budget raw.length at hUsed
  unfold budget
  omega

/-- Every component bound is a polynomial in the actual request length. -/
theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  have hOutput : PolynomiallyBounded outputBudget :=
    (PolynomiallyBounded.const _).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
  have hLinear : PolynomiallyBounded (fun L => 6*L) :=
    (PolynomiallyBounded.const 6).mul PolynomiallyBounded.id
  have hSecond : PolynomiallyBounded secondBudget :=
    ((((PolynomiallyBounded.const 5).mul FramedChooseSecondPower.budget_polynomiallyBounded).add
      hLinear).add hOutput).add (PolynomiallyBounded.const 40)
  have hFirst : PolynomiallyBounded firstBudget :=
    (((((PolynomiallyBounded.const 5).mul FramedChooseFirstPower.budget_polynomiallyBounded).add
      hLinear).add hSecond).add hOutput).add (PolynomiallyBounded.const 40)
  have hRange : PolynomiallyBounded rangeBudget :=
    (((((PolynomiallyBounded.const 5).mul (ChooseSavedCheck.budget_polynomial
      ChooseRangeDecision.budget_polynomial)).add hLinear).add hFirst).add hOutput).add
        (PolynomiallyBounded.const 40)
  exact (((((PolynomiallyBounded.const 5).mul (ChooseSavedCheck.budget_polynomial
      ChooseWidthDecision.budget_polynomial)).add hLinear).add hRange).add hOutput).add
        (PolynomiallyBounded.const 40)

end Machine.ChooseValidationRuntime
