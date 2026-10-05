import Foundation.Crypto.Semantics.Machine.NativeKeygenContinuation
import Foundation.Crypto.Semantics.Machine.RejectionContinuationDistribution

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Machine.NativeKeygenSample

private theorem sequence_layout (first second : Program) :
    first.followedBy second = Program.withSubroutine
      (first.asSubroutine 0 (first.length+1)) second [.halt]
      ((first.asSubroutine 0 (first.length+1)).length+second.length+1) := by
  simp [Program.followedBy, Program.withSubroutine, List.append_assoc,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def tail : Program := ScalarSamplePadding.program.followedBy NativeKeygenContinuation.program

def program : Program := RejectionContinuation.program tail

def charge (n : Nat) : Nat := 13*(n+3)+19+NativeKeygenContinuation.budget n

def encode (n modulus generator : Nat) (sample : List Bool) : List Bool :=
  frame (Binary.encode (n+3) (generator^Binary.value sample % modulus)) ++
    frame (Binary.encode (n+3) (Binary.value sample))

private def before (n modulus order generator : Nat) : List (Option Bool) :=
  (encodeSecurityParameter n ++ frame (Binary.encode (n+3) modulus ++
    Binary.encode (n+3) order ++ Binary.encode (n+3) generator)).reverse.map some

private theorem tail_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ tail :=
  Program.followedBy_no_randomBit _ _ ScalarSamplePadding.no_randomBit NativeKeygenContinuation.no_randomBit tape

/-- A completed retry branch pads and computes its keypair with exactly
the accepted scalar, using the actual saved request and tapes. -/
theorem completion (n modulus order generator : Nat) (leading : List Bool)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hGenerator : generator < modulus)
    (hBits : order.bits = leading++[true]) (hLeading : leading ≠ [])
    (hWidth : (leading++[true]).length ≤ n+3) :
    RejectionContinuation.Completion tail (encode n modulus generator) (charge n)
      (before n modulus order generator) (n+3) leading := by
  intro trials accepted member halted
  obtain ⟨sample, hLength, _, hInput, hOutput, hBitsSample⟩ :=
    RejectionSampling.Saved.prepared_halted_layout
      (List.replicate (n+3) (some true) ++ none::before n modulus order generator)
      leading hLeading trials accepted member halted
  obtain ⟨padded, a, ha, paddingRun, paddingHalt, retained, _, paddingOutput⟩ :=
    ScalarSamplePadding.runs_saved_layout (before n modulus order generator) (n+3)
      (leading++[true]) sample hWidth (hLength.le.trans hWidth)
  have paddingEntry : ({inputTape := {left := (leading++[true]).reverse.map some ++
      none::(List.replicate (n+3) (some true) ++ none::before n modulus order generator)}, outputTape := {left := sample.reverse.map some}} : Configuration).Equivalent (accepted.resumeAt 0) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actualPadding, actualRun, equivalent⟩ := paddingRun.exists_equivalent paddingEntry
  have actualHalt : actualPadding.halted = true := equivalent.2.1.symm.trans paddingHalt
  have sampleFit : Binary.value sample < 2^(n+3) :=
    (Binary.value_lt sample).trans_le (Nat.pow_le_pow_right (by omega) (hLength.le.trans hWidth))
  obtain ⟨keyed, b, hb, keyRun, keyHalt, keyBits⟩ := NativeKeygenContinuation.runs_numbers
    n modulus order generator (Binary.value sample) hOne hModulus hOrder sampleFit hGenerator
  have keyEntry : ({inputTape := {left := List.replicate (n+3) (some true) ++ none::before n modulus order generator}, outputTape := {left := (Binary.encode (n+3) (Binary.value sample)).reverse.map some}} : Configuration).Equivalent (actualPadding.resumeAt 0) :=
    ⟨rfl, rfl, retained.symm.trans equivalent.2.2.1, paddingOutput.symm.trans equivalent.2.2.2⟩
  obtain ⟨keys, used, bound, run, keyStopped, _, output⟩ := actualRun.followedBy_equivalent keyRun keyEntry
    (Nat.zero_le _) rfl actualHalt keyHalt
  change RunsFor tail (accepted.resumeAt 0) keys used at run
  have limit : used ≤ 13*(n+3)+18+NativeKeygenContinuation.budget n := by omega
  have evalTail : evalConfigWithin tail (accepted.resumeAt 0)
      (13*(n+3)+18+NativeKeygenContinuation.budget n) = PMF.pure keys := by
    have stopAll := run.haltsFrom_of_no_randomBit keyStopped tail_no_randomBit (le_refl used)
    rw [evalConfigWithin_eq_of_le _ _ _ _ limit stopAll]
    exact run.evalConfigWithin_eq_pure_of_no_randomBit tail_no_randomBit
  have stopBudget (c : Configuration)
      (trace : PaddedRunsFor tail (accepted.resumeAt 0) c (13*(n+3)+18+NativeKeygenContinuation.budget n)) : c.halted = true := by
    have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [evalTail] at hc
    have same : c = keys := by simpa using hc
    exact same ▸ keyStopped
  let pre := RejectionSampling.program.asSubroutine 0 RejectionContinuation.entry
  have call := Program.evalConfigWithin_withSubroutine_final_halt pre tail
    (accepted.resumeAt 0) (Nat.zero_le _) rfl (13*(n+3)+18+NativeKeygenContinuation.budget n) stopBudget
  dsimp only at call
  rw [evalTail, PMF.pure_map] at call
  let finish : Configuration := {keys with pc := pre.length+tail.length+1, halted := true}
  have layout : program = Program.withSubroutine pre tail [.halt]
      (pre.length+tail.length+1) := by
    exact sequence_layout RejectionSampling.program tail
  rw [← layout] at call
  have preLength : pre.length = RejectionContinuation.entry := by
    simp only [pre, Program.asSubroutine_length, RejectionContinuation.entry]
  have startEq : (accepted.resumeAt 0).rebasePc pre.length =
      accepted.resumeAt RejectionContinuation.entry := by
    simp only [Configuration.resumeAt, Configuration.rebasePc, preLength, Nat.add_zero]
  rw [startEq] at call
  have chargeEq : 13*(n+3)+18+NativeKeygenContinuation.budget n+1 = charge n := by
    unfold charge
    omega
  rw [chargeEq] at call
  have actual : evalConfigWithin program (accepted.resumeAt RejectionContinuation.entry) (charge n) = PMF.pure finish := call
  refine ⟨finish, rfl, ?_, ?_⟩
  · change keys.outputTape.bits = _
    have keyBitsActual : keyed.outputTape.bits = encode n modulus generator sample := keyBits
    rw [output.bits.symm, keyBitsActual, hBitsSample]
  · intro extra
    change evalConfigWithin program (accepted.resumeAt RejectionContinuation.entry) (charge n+extra) = PMF.pure finish
    rw [evalConfigWithin_add, actual, PMF.pure_bind]
    have rest : evalConfigWithin program finish extra = PMF.pure finish := by
      induction extra with
      | zero => rfl
      | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, finish]
    exact rest

/-- Exact, unrenormalized keypair distribution from the saved sampler
and native key-generation continuation, including every retry branch. -/
theorem outputMass_nat (n modulus order generator : Nat) [NeZero order]
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3)) (hTwo : 2 ≤ order)
    (hOrder : order < 2^(n+3)) (hGenerator : generator < modulus) (output : List Bool) :
    outputMassFrom program
      (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::before n modulus order generator) order.bits) output =
      ((Foundation.Probability.uniform (Fin order)).map
        (fun scalar => frame (Binary.encode (n+3) (generator^scalar.val % modulus)) ++
          frame (Binary.encode (n+3) scalar.val))) output := by
  obtain ⟨leading, hCanonical⟩ := Binary.nat_bits_canonical order (by omega)
  have hValue : Binary.value (leading++[true]) = order := by rw [← hCanonical, Binary.value_nat_bits]
  have hLeading : leading ≠ [] := by
    intro empty
    rw [empty] at hValue
    norm_num [Binary.value] at hValue
    omega
  have hLength : order.bits.length ≤ n+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hOrder
  let : Nonempty (Fin (Binary.value (leading++[true]))) := ⟨⟨0, by rw [hValue]; omega⟩⟩
  have complete := completion n modulus order generator leading hOne hModulus hOrder hGenerator hCanonical hLeading (hCanonical ▸ hLength)
  have law := RejectionContinuation.outputMass_uniform tail (encode n modulus generator) (charge n)
    (before n modulus order generator) (n+3) leading hLeading (hCanonical ▸ hLength) complete output
  have encodedLaw : ((Foundation.Probability.uniform (Fin (Binary.value (leading++[true])))).map
      (fun scalar => encode n modulus generator (Binary.encode (leading++[true]).length scalar.val))) =
      ((Foundation.Probability.uniform (Fin (Binary.value (leading++[true])))).map
        (fun scalar => frame (Binary.encode (n+3) (generator^scalar.val % modulus)) ++
          frame (Binary.encode (n+3) scalar.val))) := by
    congr 1
    funext scalar
    simp only [encode, Binary.value_encode (scalar.isLt.trans (Binary.value_lt (leading++[true])))]
  rw [encodedLaw] at law
  subst order
  simpa only [program, hCanonical] using law

def expectedBudget (n : Nat) : Nat := 24*(n+3)+24+charge n

/-- Retry time plus charged padding, exponentiation, scratch erasure,
and framing is bounded in expectation by one explicit polynomial. -/
theorem expectedSteps_nat (n modulus order generator : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3)) (hTwo : 2 ≤ order)
    (hOrder : order < 2^(n+3)) (hGenerator : generator < modulus) :
    expectedStepsFrom program
      (RejectionSampling.Saved.initial (List.replicate (n+3) (some true) ++ none::before n modulus order generator) order.bits) ≤ expectedBudget n := by
  obtain ⟨leading, hCanonical⟩ := Binary.nat_bits_canonical order (by omega)
  have hValue : Binary.value (leading++[true]) = order := by rw [← hCanonical, Binary.value_nat_bits]
  have hLeading : leading ≠ [] := by
    intro empty
    rw [empty] at hValue
    norm_num [Binary.value] at hValue
    omega
  have hLength : order.bits.length ≤ n+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hOrder
  have complete := completion n modulus order generator leading hOne hModulus hOrder hGenerator hCanonical hLeading (hCanonical ▸ hLength)
  simpa only [program, expectedBudget, ← hCanonical] using
    RejectionContinuation.expectedSteps_le tail (encode n modulus generator) (charge n)
      (before n modulus order generator) (n+3) leading hLeading (hCanonical ▸ hLength) complete

theorem expectedBudget_polynomiallyBounded : PolynomiallyBounded expectedBudget :=
  ((((PolynomiallyBounded.const 24).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3))).add
    (PolynomiallyBounded.const 24)).add
      ((((PolynomiallyBounded.const 13).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3))).add
        (PolynomiallyBounded.const 19)).add NativeKeygenContinuation.budget_polynomiallyBounded))

end Machine.NativeKeygenSample
