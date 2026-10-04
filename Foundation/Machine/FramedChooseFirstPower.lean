import Foundation.Machine.FramedChoosePowerInput
import Foundation.Machine.ChooseCandidatePower
import Foundation.Machine.ChooseSavedRequest

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Machine.FramedChooseFirstPower

private def firstReturn : Nat := FramedChoosePowerInput.program.length + 1
private def finalReturn (core : Program) : Nat := firstReturn + (ChooseCandidatePower.withCore core).length + 1
private def first : Program := FramedChoosePowerInput.program.asSubroutine 0 firstReturn

/-- Link the encoded request parser directly to candidate preparation and
the guarded modular-power machine. Both calls operate on the physical tapes
left by their predecessor. Acceptance guards and second-candidate validation
are separate obligations of the enclosing normalizer. -/
def withCore (core : Program) : Program :=
  Program.withSubroutine first (ChooseCandidatePower.withCore core) [.halt] (finalReturn core)

def program : Program := withCore BinaryPowerIsOne.program

theorem withCore_no_randomBit (core : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ core) (tape : TapeId) :
    Instruction.randomBit tape ∉ withCore core := by
  have h₁ := Program.asSubroutine_no_randomBit FramedChoosePowerInput.program
    FramedChoosePowerInput.no_randomBit 0 firstReturn tape
  have h₂ := Program.asSubroutine_no_randomBit (ChooseCandidatePower.withCore core)
    (ChooseCandidatePower.withCore_no_randomBit core h) first.length (finalReturn core) tape
  simpa only [withCore, first, Program.withSubroutine, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro h₁ h₂)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  withCore_no_randomBit BinaryPowerIsOne.program BinaryPowerIsOne.no_randomBit tape


private theorem first_layout (core : Program) : withCore core =
    Program.withSubroutine [] FramedChoosePowerInput.program
      ((ChooseCandidatePower.withCore core).asSubroutine firstReturn (finalReturn core) ++ [.halt]) firstReturn := by
  simp [withCore, first, Program.withSubroutine, firstReturn, Program.asSubroutine_length]

private theorem final_step (core : Program) (c : Configuration) (hPc : c.pc = finalReturn core)
    (hActive : c.halted = false) : Step (withCore core) c { c with halted := true } := by
  have hLookup : (withCore core)[finalReturn core]? = some .halt := by
    have hIndex : finalReturn core = first.length + (ChooseCandidatePower.withCore core).length + 1 + 0 := by
      simp [finalReturn, firstReturn, first, Program.asSubroutine_length]
    unfold withCore
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- One public polynomial budget for request preparation and the guarded
subgroup test. Conditional correctness is proved after the width guard has
exposed complete fields; malformed requests are rejected by that guard. -/
def budget (length : Nat) : Nat :=
  10000000000 * (length + 1) + 100 * (length + 1) +
    GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget length

theorem budget_polynomiallyBounded : PolynomiallyBounded budget :=
  (((PolynomiallyBounded.const 10000000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).add
    ((PolynomiallyBounded.const 100).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)))).add
        (GuardedCompiler.rawTraceBudget_polynomiallyBounded
          BinaryPowerIsOne.budget_polynomiallyBounded)

/-- A trace from the actual framed request to the subgroup-test result.
The untouched tail may contain the other candidate and arbitrary state bits.
The saved response and scratch are those of the actual guarded invocation;
there is no intermediate mathematical tape reload. -/
theorem runs_field_withCore_bounded (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (n : Nat) (modulusBits exponentBits generatorBits candidateBits tail result : List Bool)
    (hModulus : modulusBits.length = n+3)
    (hExponent : exponentBits.length = modulusBits.length)
    (hGenerator : generatorBits.length = modulusBits.length)
    (hCandidate : candidateBits.length = modulusBits.length)
    (halts : HaltsWithin core (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits)
      (q (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits).length))
    (correct : evalWithin core (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits)
      (q (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits).length) = PMF.pure (some result)) :
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generatorBits.reverse.map some ++ exponentBits.reverse.map some ++ modulusBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    let saved := none :: (false::tail).reverse.map some ++
      (DelimitedTapeComparison.marked candidateBits).reverse.map some ++ before
    ∃ c target used,
      used ≤ 10000000000 * (request.length + 1) +
        10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
        2 * columns.length + 4 + 1 + GuardedCompiler.rawTraceBudget q columns.length + 2 ∧
      RunsFor (withCore core) (Configuration.initial request) target used ∧ target.halted = true ∧
      c.halted = true ∧ c.outputBits = result ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom core columns [none] saved c).swapTapes.resumeAt
          (finalReturn core) with halted := true } : Configuration) := by
  dsimp only
  let instanceBits := modulusBits ++ exponentBits ++ generatorBits
  let body := FiniteBitEncoding.delimit candidateBits ++ tail
  let reply := false :: body
  let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
  let before := some false :: some false :: List.replicate reply.length (some true) ++
    generatorBits.reverse.map some ++ exponentBits.reverse.map some ++ modulusBits.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedChoosePowerInput.runs_valid_bounded n modulusBits exponentBits generatorBits body
      hModulus hExponent hGenerator
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedChoosePowerInput.program
    ((ChooseCandidatePower.withCore core).asSubroutine firstReturn (finalReturn core) ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor (withCore core) (Configuration.initial request) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add, request, reply] using embedded₁
  obtain ⟨c, checked, u₂, hu₂, run₂, hHalt₂, hCoreHalt, hStatus, hReturned⟩ :=
    ChooseCandidatePower.runs_field_withCore core q hNoRandom before
      (List.replicate modulusBits.length false) candidateBits exponentBits modulusBits tail result
      (by simp) hCandidate hExponent halts correct
  let canonical := DelimitedColumnSlotFill.entry
    { Tape.ofBits body with left := before }
    (Tape.ofBits (BinaryColumnSlotFill.fullSlots (List.replicate modulusBits.length false) exponentBits modulusBits))
  change RunsFor (ChooseCandidatePower.withCore core) canonical checked u₂ at run₂
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first (ChooseCandidatePower.withCore core) [.halt] (finalReturn core) (Nat.zero_le _) rfl hHalt₂
  have hCall : (canonical.rebasePc first.length).Equivalent (prepared.resumeAt firstReturn) := by
    refine ⟨?_, rfl, hInput₁.symm, hOutput₁.symm⟩
    simp [canonical, DelimitedColumnSlotFill.entry, first, firstReturn,
      Program.asSubroutine_length, Configuration.rebasePc, Configuration.resumeAt]
  have r₂ : RunsFor (withCore core) (canonical.rebasePc first.length)
      (checked.resumeAt (finalReturn core)) v₂ := embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalReturn core := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨c, { actual with halted := true }, v₁+v₂+1,
    by
      dsimp only [request, reply, body, instanceBits, columns] at *
      simp only [List.cons_append, List.append_assoc] at *
      omega,
    (r₁.trans actualRun₂).succ (final_step core actual hPc hActive), rfl,
    hCoreHalt, hStatus, ?_⟩
  exact ⟨hPc, rfl, hActual.2.2.1.symm.trans hReturned.2.2.1,
    hActual.2.2.2.symm.trans hReturned.2.2.2⟩


theorem runs_field_withCore (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (n : Nat) (modulusBits exponentBits generatorBits candidateBits tail result : List Bool)
    (hModulus : modulusBits.length = n+3)
    (hExponent : exponentBits.length = modulusBits.length)
    (hGenerator : generatorBits.length = modulusBits.length)
    (hCandidate : candidateBits.length = modulusBits.length)
    (halts : HaltsWithin core (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits)
      (q (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits).length))
    (correct : evalWithin core (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits)
      (q (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits).length) = PMF.pure (some result)) :
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generatorBits.reverse.map some ++ exponentBits.reverse.map some ++ modulusBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    let saved := none :: (false::tail).reverse.map some ++
      (DelimitedTapeComparison.marked candidateBits).reverse.map some ++ before
    ∃ c target used,
      RunsFor (withCore core) (Configuration.initial request) target used ∧ target.halted = true ∧
      c.halted = true ∧ c.outputBits = result ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom core columns [none] saved c).swapTapes.resumeAt
          (finalReturn core) with halted := true } : Configuration) := by
  obtain ⟨c, target, used, _, run, hHalt, hCoreHalt, hBits, hReturned⟩ :=
    runs_field_withCore_bounded core q hNoRandom n modulusBits exponentBits generatorBits
      candidateBits tail result hModulus hExponent hGenerator hCandidate halts correct
  exact ⟨c, target, used, run, hHalt, hCoreHalt, hBits, hReturned⟩

/-- Complete equal-width fields reach a halted subgroup call regardless
of their numeric values. The core's all-input stopping theorem, rather than
arithmetic correctness assumptions, supplies termination for this branch. -/
theorem runs_fields_terminating (core : Program) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ core)
    (n : Nat) (modulusBits exponentBits generatorBits candidateBits tail : List Bool)
    (hModulus : modulusBits.length = n+3)
    (hExponent : exponentBits.length = modulusBits.length)
    (hGenerator : generatorBits.length = modulusBits.length)
    (hCandidate : candidateBits.length = modulusBits.length)
    (halts : HaltsWithin core (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits)
      (q (BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits).length)) :
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    ∃ target used,
      used ≤ 10000000000 * (request.length + 1) +
        10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
        2 * columns.length + 4 + 1 + GuardedCompiler.rawTraceBudget q columns.length + 2 ∧
      RunsFor (withCore core) (Configuration.initial request) target used ∧ target.halted = true := by
  dsimp only
  let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
  obtain ⟨source, u, _, sourceRun, sourceHalt⟩ :=
    exists_halted_run_of_haltsFrom core (Configuration.initial columns) (q columns.length) halts
  have sourceCorrect : evalWithin core columns (q columns.length) =
      PMF.pure (some source.outputBits) := by
    have hWith : HaltsWith core columns source.outputBits u :=
      ⟨source, sourceRun, sourceHalt, rfl⟩
    rw [evalWithin_eq_of_haltsWithin core columns (q columns.length) u halts
      (hWith.haltsWithin_of_no_randomBit hNoRandom)]
    exact hWith.evalWithin_eq_pure_of_no_randomBit hNoRandom
  obtain ⟨c, target, used, hUsed, run, hHalt, _, _, _⟩ :=
    runs_field_withCore_bounded core q hNoRandom n modulusBits exponentBits generatorBits
      candidateBits tail source.outputBits hModulus hExponent hGenerator hCandidate
      halts sourceCorrect
  exact ⟨target, used, hUsed, run, hHalt⟩

/-- Once the width guard has exposed complete equal-width fields, the
actual subgroup code stops at the public request-length polynomial budget.
Numeric range or primality assumptions are not needed for this stopping fact. -/
theorem runs_fields_bounded (n : Nat) (modulusBits exponentBits generatorBits candidateBits tail : List Bool)
    (hModulus : modulusBits.length = n+3)
    (hExponent : exponentBits.length = modulusBits.length)
    (hGenerator : generatorBits.length = modulusBits.length)
    (hCandidate : candidateBits.length = modulusBits.length)
:
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    ∃ target used,
      used ≤ budget request.length ∧
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt⟩ :=
    runs_fields_terminating BinaryPowerIsOne.program BinaryPowerIsOne.budget
      BinaryPowerIsOne.no_randomBit n modulusBits exponentBits generatorBits candidateBits tail
      hModulus hExponent hGenerator hCandidate (BinaryPowerIsOne.haltsWithin _)
  let request := encodeSecurityParameter n ++ frame (modulusBits ++ exponentBits ++ generatorBits) ++
    frame (false :: FiniteBitEncoding.delimit candidateBits ++ tail)
  let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
  have hSizes : candidateBits.length ≤ request.length ∧ tail.length ≤ request.length ∧
      columns.length ≤ request.length := by
    simp [request, columns, BinaryColumnSlotFill.fullSlots_length,
      encodeSecurityParameter, frame, hCandidate, hExponent, hGenerator, hModulus] <;> omega
  have hTrace := GuardedCompiler.rawTraceBudget_monotone
    BinaryPowerIsOne.budget_monotone hSizes.2.2
  refine ⟨target, used, ?_, run, hHalt⟩
  change used ≤ budget request.length
  change used ≤ 10000000000 * (request.length + 1) + 100 * (request.length + 1) +
    GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget request.length
  change used ≤ 10000000000 * (request.length + 1) +
    10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
    2 * columns.length + 4 + 1 +
    GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget columns.length + 2 at hUsed
  simp only [List.length_cons] at hUsed
  omega

/-- A singleton native decision and the real saved-request layout are
retained together with the public stopping bound, without numeric hypotheses. -/
theorem runs_fields_decision_bounded (n : Nat) (modulusBits exponentBits generatorBits candidateBits tail : List Bool)
    (hModulus : modulusBits.length = n+3)
    (hExponent : exponentBits.length = modulusBits.length)
    (hGenerator : generatorBits.length = modulusBits.length)
    (hCandidate : candidateBits.length = modulusBits.length)
:
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    ∃ (c target : Configuration) (used : Nat) (status : Bool),
      used ≤ budget request.length ∧
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true ∧
      c.outputBits = [status] ∧
      (target.resumeAt 0).Equivalent
        (((GuardedCompiler.rawResultFrom BinaryPowerIsOne.program columns [none]
          (none :: request.reverse.map some) c).swapTapes).resumeAt 0) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame (modulusBits ++ exponentBits ++ generatorBits) ++
    frame (false :: FiniteBitEncoding.delimit candidateBits ++ tail)
  let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
  obtain ⟨powerTarget, powerUsed, bits, finish, coreUsed, hCoreUsed, _, _, _,
    coreRun, coreHalt, _, coreBits⟩ := BinaryPowerIsOne.runs_any columns
  let status := BinaryIsOneInPlace.accepts bits
  have coreCorrect : evalWithin BinaryPowerIsOne.program columns
      (BinaryPowerIsOne.budget columns.length) = PMF.pure (some [status]) := by
    have hWith : HaltsWith BinaryPowerIsOne.program columns [status] coreUsed :=
      ⟨finish, coreRun, coreHalt, coreBits⟩
    rw [evalWithin_eq_of_haltsWithin BinaryPowerIsOne.program columns
      (BinaryPowerIsOne.budget columns.length) coreUsed
      (BinaryPowerIsOne.haltsWithin columns)
      (hWith.haltsWithin_of_no_randomBit BinaryPowerIsOne.no_randomBit)]
    exact hWith.evalWithin_eq_pure_of_no_randomBit BinaryPowerIsOne.no_randomBit
  obtain ⟨c, target, used, hUsed, run, hHalt, _, hBits, hReturned⟩ :=
    runs_field_withCore_bounded BinaryPowerIsOne.program BinaryPowerIsOne.budget
      BinaryPowerIsOne.no_randomBit n modulusBits exponentBits generatorBits candidateBits tail [status]
      hModulus hExponent hGenerator hCandidate (BinaryPowerIsOne.haltsWithin columns) coreCorrect
  have hSizes : candidateBits.length ≤ request.length ∧ tail.length ≤ request.length ∧
      columns.length ≤ request.length := by
    simp [request, columns, BinaryColumnSlotFill.fullSlots_length,
      encodeSecurityParameter, frame, hCandidate, hExponent, hGenerator, hModulus] <;> omega
  have hTrace := GuardedCompiler.rawTraceBudget_monotone
    BinaryPowerIsOne.budget_monotone hSizes.2.2
  refine ⟨c, target, used, status, ?_, run, hHalt, hBits, ?_⟩
  · change used ≤ budget request.length
    change used ≤ 10000000000 * (request.length + 1) + 100 * (request.length + 1) +
      GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget request.length
    change used ≤ 10000000000 * (request.length + 1) +
      10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
      2 * columns.length + 4 + 1 +
      GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget columns.length + 2 at hUsed
    simp only [List.length_cons] at hUsed
    omega
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa only [ChooseSavedRequest.first_candidate_saved,
        Configuration.resumeAt] using hReturned.2.2.1
    · simpa only [ChooseSavedRequest.first_candidate_saved,
        Configuration.resumeAt] using hReturned.2.2.2

/-- Instantiate the linked native request trace with the actual modular
power-and-one-test code, including its proved stopping bound and numerical
correctness. This is the first candidate's subgroup predicate, rather than
an assumed arithmetic operation in the outer parser. -/
theorem runs_numbers (n modulus exponent generator candidate : Nat)
    (hOne : 1 < modulus) (hCandidate : candidate < modulus)
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (tail : List Bool) :
    let width := n+3
    let modulusBits := Binary.encode width modulus
    let exponentBits := Binary.encode width exponent
    let generatorBits := Binary.encode width generator
    let candidateBits := Binary.encode width candidate
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    let saved := none :: request.reverse.map some
    ∃ c target used,
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true ∧
      c.halted = true ∧
      c.outputBits = [BinaryIsOneInPlace.accepts (Binary.encode width (candidate ^ exponent % modulus))] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom BinaryPowerIsOne.program columns [none] saved c).swapTapes.resumeAt
          (finalReturn BinaryPowerIsOne.program) with halted := true } : Configuration) := by
  simpa only [program, ChooseSavedRequest.first_candidate_saved] using
    runs_field_withCore BinaryPowerIsOne.program BinaryPowerIsOne.budget
      BinaryPowerIsOne.no_randomBit n (Binary.encode (n+3) modulus) (Binary.encode (n+3) exponent)
      (Binary.encode (n+3) generator) (Binary.encode (n+3) candidate) tail
      [BinaryIsOneInPlace.accepts (Binary.encode (n+3) (candidate ^ exponent % modulus))]
      (by simp) (by simp) (by simp) (by simp)
      (BinaryPowerIsOne.haltsWithin _)
      (BinaryPowerIsOne.eval_numbers (n+3) modulus candidate exponent hOne hCandidate hExponent hModulus)

/-- The actual subgroup trace has a stopping bound polynomial in the
whole framed request, including arbitrary trailing adversary state. -/
theorem runs_numbers_bounded (n modulus exponent generator candidate : Nat)
    (hOne : 1 < modulus) (hCandidate : candidate < modulus)
    (hExponent : exponent < 2 ^ (n+3)) (hModulus : modulus < 2 ^ (n+3))
    (tail : List Bool) :
    let width := n+3
    let modulusBits := Binary.encode width modulus
    let exponentBits := Binary.encode width exponent
    let generatorBits := Binary.encode width generator
    let candidateBits := Binary.encode width candidate
    let instanceBits := modulusBits ++ exponentBits ++ generatorBits
    let reply := false :: FiniteBitEncoding.delimit candidateBits ++ tail
    let request := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
    let saved := none :: request.reverse.map some
    ∃ c target used, used ≤ budget request.length ∧
      RunsFor program (Configuration.initial request) target used ∧ target.halted = true ∧
      c.halted = true ∧
      c.outputBits = [BinaryIsOneInPlace.accepts (Binary.encode width (candidate ^ exponent % modulus))] ∧
      target.Equivalent
        ({ (GuardedCompiler.rawResultFrom BinaryPowerIsOne.program columns [none] saved c).swapTapes.resumeAt
          (finalReturn BinaryPowerIsOne.program) with halted := true } : Configuration) := by
  have result :=
    runs_field_withCore_bounded BinaryPowerIsOne.program BinaryPowerIsOne.budget
      BinaryPowerIsOne.no_randomBit n (Binary.encode (n+3) modulus) (Binary.encode (n+3) exponent)
      (Binary.encode (n+3) generator) (Binary.encode (n+3) candidate) tail
      [BinaryIsOneInPlace.accepts (Binary.encode (n+3) (candidate ^ exponent % modulus))]
      (by simp) (by simp) (by simp) (by simp)
      (BinaryPowerIsOne.haltsWithin _)
      (BinaryPowerIsOne.eval_numbers (n+3) modulus candidate exponent hOne hCandidate hExponent hModulus)

  obtain ⟨c, target, used, hUsed, run, hHalt, hCoreHalt, hBits, hReturned⟩ := result
  let modulusBits := Binary.encode (n+3) modulus
  let exponentBits := Binary.encode (n+3) exponent
  let generatorBits := Binary.encode (n+3) generator
  let candidateBits := Binary.encode (n+3) candidate
  let request := encodeSecurityParameter n ++ frame (modulusBits ++ exponentBits ++ generatorBits) ++
    frame (false :: FiniteBitEncoding.delimit candidateBits ++ tail)
  let columns := BinaryColumnSlotFill.fullSlots candidateBits exponentBits modulusBits
  have hSizes : candidateBits.length ≤ request.length ∧ tail.length ≤ request.length ∧
      columns.length ≤ request.length := by
    simp [request, candidateBits, modulusBits, exponentBits, generatorBits,
      columns, BinaryColumnSlotFill.fullSlots_length,
      encodeSecurityParameter, frame,
      ] <;> omega
  have hTrace := GuardedCompiler.rawTraceBudget_monotone
    BinaryPowerIsOne.budget_monotone hSizes.2.2
  refine ⟨c, target, used, ?_, run, hHalt, hCoreHalt, hBits, ?_⟩
  · change used ≤ budget request.length
    change used ≤ 10000000000 * (request.length + 1) + 100 * (request.length + 1) +
      GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget request.length
    change used ≤ 10000000000 * (request.length + 1) +
      10 * candidateBits.length + 2 + 3 * (false :: tail).length + 3 +
      2 * columns.length + 4 + 1 +
      GuardedCompiler.rawTraceBudget BinaryPowerIsOne.budget columns.length + 2 at hUsed
    simp only [List.length_cons] at hUsed
    omega
  · simpa only [ChooseSavedRequest.first_candidate_saved] using hReturned


end Machine.FramedChooseFirstPower
