import Foundation.Constructions.ElGamal.PrimeOrderChooseNormalization
import Foundation.Machine.ChooseValidation
import Foundation.Machine.ChooseSafeValidation

namespace ElGamal.PrimeOrderRepresentation

/-- Complete operational correctness of the connected finite validation
body on two complete fixed-width fields. Candidate validity is established
by the real range and subgroup programs, not supplied as a premise. -/
theorem chooseValidation_fields_runs_normalization
    (n : Nat) (x : Domain n) (first second state : List Bool)
    (hFirst : first.length = n+3) (hSecond : second.length = n+3) :
    ∃ target used,
      Machine.RunsFor Machine.ChooseValidation.program
        (Machine.Configuration.initial
          (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
            Machine.frame (Machine.canonicalMessageBits first second state))) target used ∧
      target.halted = true ∧ target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator
        (Machine.canonicalMessageBits first second state) := by
  let C := x.down
  let reply := Machine.canonicalMessageBits first second state
  let firstStatus := Machine.BinaryIsOneInPlace.accepts
    (Machine.Binary.encode (n+3) (Machine.Binary.value first ^ C.scalarOrder % C.modulus))
  let secondStatus := Machine.BinaryIsOneInPlace.accepts
    (Machine.Binary.encode (n+3) (Machine.Binary.value second ^ C.scalarOrder % C.modulus))
  let accepted := decide (Machine.Binary.value first < C.modulus ∧
    Machine.Binary.value second < C.modulus) && (firstStatus && secondStatus)
  have hFirstStatus : firstStatus = true ↔
      Machine.Binary.value first ^ C.scalarOrder % C.modulus = 1 := by
    rw [Machine.BinaryIsOneInPlace.accepts_iff_value_one,
      Machine.Binary.value_encode ((Nat.mod_lt _ C.modulus_prime.pos).trans C.modulus_lt)]
  have hSecondStatus : secondStatus = true ↔
      Machine.Binary.value second ^ C.scalarOrder % C.modulus = 1 := by
    rw [Machine.BinaryIsOneInPlace.accepts_iff_value_one,
      Machine.Binary.value_encode ((Nat.mod_lt _ C.modulus_prime.pos).trans C.modulus_lt)]
  have hAccepted : accepted = true ↔
      (Machine.Binary.value first < C.modulus ∧ Machine.Binary.value second < C.modulus) ∧
      (Machine.Binary.value first ^ C.scalarOrder % C.modulus = 1 ∧
        Machine.Binary.value second ^ C.scalarOrder % C.modulus = 1) := by
    simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, hFirstStatus, hSecondStatus]
  have hValid : (∃ m₀ m₁ s,
      (responseCodeOfElement (elementCode n x)).decode reply = some (.inl (m₀, m₁, s))) ↔
      accepted = true := by
    rw [validChooseResponse_iff_numeric_without_nonzero, hAccepted]
    constructor
    · rintro ⟨a, b, s, hLayout, _, hRangeA, hPowerA, _, hRangeB, hPowerB⟩
      have hParse := congrArg (fun bits => Machine.FiniteBitEncoding.undelimit bits.tail) hLayout
      simp only [reply, Machine.canonicalMessageBits, List.tail_cons, List.append_assoc,
        Machine.FiniteBitEncoding.undelimit_delimit, Option.some.injEq, Prod.mk.injEq] at hParse
      have hParseSecond := congrArg Machine.FiniteBitEncoding.undelimit hParse.2
      simp only [Machine.FiniteBitEncoding.undelimit_delimit,
        Option.some.injEq, Prod.mk.injEq] at hParseSecond
      rcases hParse with ⟨rfl, _⟩
      rcases hParseSecond with ⟨rfl, _⟩
      exact ⟨⟨hRangeA, hRangeB⟩, hPowerA, hPowerB⟩
    · rintro ⟨⟨hRangeA, hRangeB⟩, hPowerA, hPowerB⟩
      exact ⟨first, second, state, rfl, hFirst, hRangeA, hPowerA,
        hSecond, hRangeB, hPowerB⟩
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    Machine.ChooseValidation.runs_fields n C.modulus C.scalarOrder C.generator.val.val
      C.modulus_prime.one_lt (C.scalarOrder_lt_modulus.trans C.modulus_lt) C.modulus_lt
      first second state hFirst hSecond
  change target.outputBits = (if accepted then reply else Machine.canonicalMessageBits
    (Machine.Binary.encode (n+3) C.generator.val.val)
    (Machine.Binary.encode (n+3) C.generator.val.val) []) at hBits
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [C, instanceCode, PrimeOrderParameters.instanceCode, List.append_assoc] using run
  · cases hDecision : accepted with
    | true =>
        obtain ⟨m₀, m₁, s, hDecode⟩ := hValid.mpr hDecision
        rw [normalizeChooseResponse_eq_self_of_valid n x reply m₀ m₁ s hDecode]
        simpa only [hDecision, ↓reduceIte] using hBits
    | false =>
        have hInvalid : ¬ ∃ m₀ m₁ s,
            (responseCodeOfElement (elementCode n x)).decode reply = some (.inl (m₀, m₁, s)) := by
          intro h
          have hTrue := hValid.mp h
          simp only [hDecision, Bool.false_eq_true] at hTrue
        rw [normalizeChooseResponse_eq_default_of_invalid n x reply hInvalid]
        rw [hDecision] at hBits
        simpa [C, elementCode,
          PrimeOrderParameters.elementCode, embed, PrimeOrderParameters.parameters] using hBits

/-- Every finite adversary response, including missing delimiters, wrong
lengths, empty replies, and wrong-stage tags, is normalized by the connected
native code on an actual represented instance request. This is a semantic
trace theorem; a common all-input stopping budget still needs its guard. -/
theorem chooseValidation_runs_normalization
    (n : Nat) (x : Domain n) (bits : List Bool) :
    ∃ target used,
      Machine.RunsFor Machine.ChooseValidation.program
        (Machine.Configuration.initial
          (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
            Machine.frame bits)) target used ∧
      target.halted = true ∧ target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits := by
  let C := x.down
  let p := Machine.Binary.encode (n+3) C.modulus
  let q := Machine.Binary.encode (n+3) C.scalarOrder
  let g := Machine.Binary.encode (n+3) C.generator.val.val
  have hDefault (reply : List Bool)
      (hInvalid : ¬ ∃ m₀ m₁ state,
        (responseCodeOfElement (elementCode n x)).decode reply = some (.inl (m₀, m₁, state)))
      (hRun : ∃ target used,
        Machine.RunsFor Machine.ChooseValidation.program
          (Machine.Configuration.initial (Machine.encodeSecurityParameter n ++
            Machine.frame (p ++ q ++ g) ++ Machine.frame reply)) target used ∧
        target.halted = true ∧ target.outputBits = Machine.canonicalMessageBits g g []) :
      ∃ target used,
        Machine.RunsFor Machine.ChooseValidation.program
          (Machine.Configuration.initial (Machine.encodeSecurityParameter n ++
            Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply)) target used ∧
        target.halted = true ∧ target.outputBits = normalizeChooseResponse
          (elementCode n x) (embed n x).params.generator reply := by
    obtain ⟨target, used, run, hHalt, hOutput⟩ := hRun
    refine ⟨target, used, ?_, hHalt, ?_⟩
    · simpa [C, p, q, g, instanceCode, PrimeOrderParameters.instanceCode,
        List.append_assoc] using run
    · rw [normalizeChooseResponse_eq_default_of_invalid n x reply hInvalid]
      simpa [C, g, elementCode, PrimeOrderParameters.elementCode,
        embed, PrimeOrderParameters.parameters] using hOutput
  have hWrongTag (reply : List Bool)
      (hTag : (Machine.Tape.ofBits reply).current = none ∨
        (Machine.Tape.ofBits reply).current = some true) :
      ∃ target used,
        Machine.RunsFor Machine.ChooseValidation.program
          (Machine.Configuration.initial (Machine.encodeSecurityParameter n ++
            Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply)) target used ∧
        target.halted = true ∧ target.outputBits = normalizeChooseResponse
          (elementCode n x) (embed n x).params.generator reply := by
    apply hDefault reply
    · intro hValid
      obtain ⟨first, second, state, hLayout, _⟩ :=
        (validChooseResponse_iff_numeric_without_nonzero n x reply).mp hValid
      have hHead : (Machine.Tape.ofBits reply).current = some false := by
        simpa only [Machine.canonicalMessageBits, Machine.Tape.ofBits] using
          congrArg (fun bs => (Machine.Tape.ofBits bs).current) hLayout
      rw [hHead] at hTag
      simp at hTag
    · exact Machine.ChooseValidation.runs_wrong_tag n p q g reply
        (by simp [p]) (by simp [p, q]) (by simp [p, g]) hTag
  cases bits with
  | nil => exact hWrongTag [] (Or.inl rfl)
  | cons tag payload =>
    cases tag with
    | true => exact hWrongTag (true :: payload) (Or.inr rfl)
    | false =>
      let widths := (Machine.FiniteBitEncoding.undelimit payload).any (fun pair =>
        decide (pair.1.length = n+3) &&
          (Machine.FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = n+3)))
      cases hWidth : widths with
      | false =>
        apply hDefault (false :: payload)
        · intro hValid
          obtain ⟨first, second, state, hLayout, hFirst, _, _, hSecond, _⟩ :=
            (validChooseResponse_iff_numeric_without_nonzero n x (false :: payload)).mp hValid
          have hPayload := congrArg List.tail hLayout
          simp only [Machine.canonicalMessageBits, List.tail_cons] at hPayload
          have hWidthTrue : widths = true := by
            simp [widths, hPayload, List.append_assoc, hFirst, hSecond]
          simp only [hWidth, Bool.false_eq_true] at hWidthTrue
        · exact Machine.ChooseValidation.runs_rejected_widths n p q g payload
            (by simp [p]) (by simp [p, q]) (by simp [p, g]) hWidth
      | true =>
        cases hParseFirst : Machine.FiniteBitEncoding.undelimit payload with
        | none => simp [widths, hParseFirst] at hWidth
        | some pair =>
          rcases pair with ⟨first, remainder⟩
          cases hParseSecond : Machine.FiniteBitEncoding.undelimit remainder with
          | none => simp [widths, hParseFirst, hParseSecond] at hWidth
          | some pair =>
            rcases pair with ⟨second, state⟩
            have hLengths : first.length = n+3 ∧ second.length = n+3 := by
              simpa [widths, hParseFirst, hParseSecond] using hWidth
            have hFirst := Machine.FiniteBitEncoding.delimit_append_of_undelimit hParseFirst
            have hSecond := Machine.FiniteBitEncoding.delimit_append_of_undelimit hParseSecond
            have hLayout : Machine.canonicalMessageBits first second state = false :: payload := by
              simp only [Machine.canonicalMessageBits, List.cons.injEq, true_and]
              rw [List.append_assoc, hSecond]
              exact hFirst
            simpa only [hLayout] using
              chooseValidation_fields_runs_normalization n x first second state hLengths.1 hLengths.2

/-- The outer guard and validation body are one fixed finite program.
Every finite reply on a represented instance reaches the specified exact
normalization output. The following evaluator theorem connects this trace
to the common all-input stopping budget. -/
theorem chooseSafeValidation_runs_normalization
    (n : Nat) (x : Domain n) (bits : List Bool) :
    ∃ target used,
      Machine.RunsFor Machine.ChooseSafeValidation.program
        (Machine.Configuration.initial
          (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
            Machine.frame bits)) target used ∧
      target.halted = true ∧ target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits := by
  obtain ⟨next, bodyUsed, bodyRun, bodyHalt, hOutput⟩ := chooseValidation_runs_normalization n x bits
  obtain ⟨target, used, _, run, hHalt, hBits⟩ :=
    Machine.ChooseSafeValidation.runs_valid n ((instanceCode n).encode x) bits
      (instanceCode_length n x) next bodyUsed bodyRun bodyHalt
  exact ⟨target, used, run, hHalt, hBits.trans hOutput⟩

/-- The same public polynomial budget applies to correct represented requests
and to every malformed finite raw input. -/
theorem chooseSafeValidation_eval_normalization
    (n : Nat) (x : Domain n) (bits : List Bool) :
    let raw := Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
      Machine.frame bits
    Machine.evalWithin Machine.ChooseSafeValidation.program raw
      (Machine.ChooseSafeValidation.budget raw.length) = PMF.pure (some (normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits)) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hOutput⟩ := chooseSafeValidation_runs_normalization n x bits
  have hWith : Machine.HaltsWith Machine.ChooseSafeValidation.program _ _ used :=
    ⟨target, run, hHalt, hOutput⟩
  rw [Machine.evalWithin_eq_of_haltsWithin Machine.ChooseSafeValidation.program _
    (Machine.ChooseSafeValidation.budget _) used (Machine.ChooseSafeValidation.haltsWithin _)
    (hWith.haltsWithin_of_no_randomBit Machine.ChooseSafeValidation.no_randomBit)]
  exact hWith.evalWithin_eq_pure_of_no_randomBit Machine.ChooseSafeValidation.no_randomBit

/-- Concrete finite normalization code: exact decoder behavior on every reply,
including arbitrary state, with all-input polynomial stopping. -/
noncomputable def chooseNormalizer : RepresentedChooseNormalizer simulatorPrimitives where
  program := Machine.ChooseSafeValidation.program
  budget := Machine.ChooseSafeValidation.budget
  budget_polynomial := Machine.ChooseSafeValidation.budget_polynomiallyBounded
  halts := Machine.ChooseSafeValidation.haltsWithin
  correct := chooseSafeValidation_eval_normalization

end ElGamal.PrimeOrderRepresentation
