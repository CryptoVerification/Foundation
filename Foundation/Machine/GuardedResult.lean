import Foundation.Machine.GuardedExecution
import Foundation.Machine.GuardedOutput

namespace Machine.GuardedCompiler

/-- The actual source-call continuation, after input preparation and the
compiled source block including its explicit return jump. -/
def resultEntry (source : Program) : Nat := 87 + (compile source).length + 1

/-- Complete finite code on raw inputs: charged guarded-tape preparation,
guarded simulation, charged raw-output extraction, and an actual final halt.
Neither caller tape initialization nor output decoding is a primitive. -/
def rawCompile (source : Program) : Program :=
  Program.withSubroutine (prepareTapes.asSubroutine 0 87) (compile source)
    (extractOutput.asSubroutine (resultEntry source) (resultEntry source + 65) ++ [.halt])
    (resultEntry source)

theorem rawCompile_length (source : Program) :
    (rawCompile source).length = 68 * source.length + 155 := by
  simp [rawCompile, Program.withSubroutine, compile_length, blockSize,
    show prepareTapes.length = 86 from rfl, show extractOutput.length = 64 from rfl]
  omega

def resultBudget (q : Nat → Nat) (m : Nat) : Nat :=
  28 * (2 * m + 2 + q m) + 27

def rawTraceBudget (q : Nat → Nat) (m : Nat) : Nat :=
  31 * m + 42 + preparedTraceBudget q m + resultBudget q m

/-- Full result with caller-owned prefixes retained on both physical tapes.
The simulated source sees only its guarded logical tapes. -/
def rawResultFrom (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) : Configuration :=
  { extractOutputFinish (input.reverse.map some ++ beforeInput) beforeOutput c.inputTape c.outputTape with
    pc := resultEntry source + 65 }


/-- Physical storage after the charged raw-result extraction, including
both caller prefixes and the guarded source scratch. No replacement of
tapes or decoded-response assumption occurs in this size estimate. -/
theorem rawResultFrom_sourceStorage_le (source : Program) (request : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) :
    sourceStorage (rawResultFrom source request beforeInput beforeOutput c) ≤
      20 * (request.length + beforeInput.length + beforeOutput.length + sourceStorage c + 1) := by
  have hBits := Tape.bits_length_le_cells c.outputTape
  have hPadding := Nat.sub_le (2 * c.outputTape.cells + 2) c.outputBits.length
  simp only [rawResultFrom, extractOutputFinish, copyScratchFinish, sourceStorage, Tape.cells,
    List.length_append, List.length_cons, List.length_nil, List.length_reverse,
    List.length_map, List.length_replicate, scratchPrefix, encodeTape,
    VirtualCell.pairTape, encodedLeftCells_length, encodedRightBits_length,
    Configuration.outputBits] at *
  omega

def rawResult (source : Program) (input : List Bool) (c : Configuration) : Configuration :=
  { extractOutputFinish (input.reverse.map some) [] c.inputTape c.outputTape with
    pc := resultEntry source + 65 }

theorem rawResultFrom_empty (source : Program) (input : List Bool) :
    rawResultFrom source input [] [] = rawResult source input := by
  funext c
  simp only [rawResultFrom, rawResult, List.append_nil]

private theorem halted_eval (p : Program) (c : Configuration) (hHalted : c.halted = true)
    (steps : Nat) : evalConfigWithin p c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, hHalted]

theorem rawCompile_prepare_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (rawCompile source) (packInputStart beforeInput beforeOutput input) (31 * input.length + 42) =
      PMF.pure ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
        (preparedSource input)).rebasePc 87) := by
  have h := prepareTapes_withSubroutine_eval []
    ((compile source).asSubroutine 87 (resultEntry source) ++
      extractOutput.asSubroutine (resultEntry source) (resultEntry source + 65) ++ [.halt])
    87 beforeInput beforeOutput input
  have hProgram : Program.withSubroutine [] prepareTapes
      ((compile source).asSubroutine 87 (resultEntry source) ++
        extractOutput.asSubroutine (resultEntry source) (resultEntry source + 65) ++ [.halt]) 87 =
      rawCompile source := by
    simp only [rawCompile, Program.withSubroutine, List.length_nil, List.nil_append,
      show (prepareTapes.asSubroutine 0 87).length = 87 from rfl, List.append_assoc]
  rw [hProgram] at h
  change evalConfigWithin (rawCompile source) (packInputStart beforeInput beforeOutput input)
    (31 * input.length + 42) = PMF.pure ((prepareTapesFinish beforeInput beforeOutput input).resumeAt 87) at h
  have hEntry : (prepareTapesFinish beforeInput beforeOutput input).resumeAt 87 =
      (encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
        (preparedSource input)).rebasePc 87 := by
    simp [prepareTapesFinish, Configuration.resumeAt, Configuration.rebasePc,
      encodeConfiguration, address, preparedSource]
  exact h.trans (congrArg PMF.pure hEntry)

theorem rawCompile_prepare_eval (source : Program) (input : List Bool) :
    evalConfigWithin (rawCompile source) (Configuration.initial input) (31 * input.length + 42) =
      PMF.pure ((encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87) := by
  have h := rawCompile_prepare_eval_from source input [] []
  have hInitial : packInputStart [] [] input = Configuration.initial input := by cases input <;> rfl
  rw [hInitial] at h
  simpa only [List.append_nil] using h

private theorem rawCompile_extraction_layout (source : Program) :
    rawCompile source = Program.withSubroutine
      (prepareTapes.asSubroutine 0 87 ++ (compile source).asSubroutine 87 (resultEntry source))
      extractOutput [.halt] (resultEntry source + 65) := by
  simp only [rawCompile, Program.withSubroutine, Program.asSubroutine_length]
  have hBase : (prepareTapes.asSubroutine 0 87 ++
      (compile source).asSubroutine 87 (resultEntry source)).length = resultEntry source := by
    simp [resultEntry, show prepareTapes.length = 86 from rfl, Nat.add_assoc]
  simp only [hBase, List.append_assoc]
  rfl

/-- Exact operational extraction followed by the caller's charged halt,
from the physical tapes delivered by a returned source branch. -/
theorem rawCompile_extract_exact_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput c).resumeAt (resultEntry source))
      (extractOutputSteps c.inputTape c.outputTape + 1) = PMF.pure (rawResultFrom source input beforeInput beforeOutput c) := by
  let pre := prepareTapes.asSubroutine 0 87 ++ (compile source).asSubroutine 87 (resultEntry source)
  have hPre : pre.length = resultEntry source := by
    simp [pre, resultEntry, show prepareTapes.length = 86 from rfl, Nat.add_assoc]
  have hExtract := extractOutput_withSubroutine_eval pre [.halt] (resultEntry source + 65)
    (input.reverse.map some ++ beforeInput) beforeOutput c.inputTape c.outputTape
  have hStart : (extractToScratchStart (input.reverse.map some ++ beforeInput) beforeOutput c.inputTape c.outputTape).rebasePc
      pre.length =
      (encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput c).resumeAt (resultEntry source) := by
    simp [extractToScratchStart, VirtualCell.start, Configuration.rebasePc,
      Configuration.resumeAt, encodeConfiguration, hPre]
  rw [hStart, ← rawCompile_extraction_layout] at hExtract
  rw [evalConfigWithin_add, hExtract, PMF.pure_bind]
  have hInstr : (rawCompile source)[resultEntry source + 65]? = some .halt := by
    rw [rawCompile_extraction_layout]
    have h := Program.withSubroutine_getElem?_suffix pre extractOutput [.halt]
      (resultEntry source + 65) 0
    simpa [pre, hPre, extractOutput, extractToScratch, seekScratchInput, rewindRegion,
      decodeRegion, clearOutputGuard, rewindBitstring, copyBitstring] using h
  have hPc : ((extractOutputFinish (input.reverse.map some ++ beforeInput) beforeOutput c.inputTape c.outputTape).resumeAt
      (resultEntry source + 65)).pc = resultEntry source + 65 := rfl
  simp only [evalConfigWithin, PMF.pure_bind, stepPMF, next, Configuration.halted_resumeAt,
    Bool.false_eq_true, ↓reduceIte, hPc, hInstr, Instruction.next]
  rfl

theorem rawCompile_extract_exact_eval (source : Program) (input : List Bool) (c : Configuration) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some) [] c).resumeAt (resultEntry source))
      (extractOutputSteps c.inputTape c.outputTape + 1) = PMF.pure (rawResult source input c) := by
  simpa only [List.append_nil, rawResultFrom_empty] using rawCompile_extract_exact_eval_from source input [] [] c

theorem rawCompile_extract_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration)
    (budget : Nat) (hFits : extractOutputSteps c.inputTape c.outputTape + 1 ≤ budget) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput c).resumeAt (resultEntry source))
      budget = PMF.pure (rawResultFrom source input beforeInput beforeOutput c) := by
  rw [show budget = (extractOutputSteps c.inputTape c.outputTape + 1) +
      (budget - (extractOutputSteps c.inputTape c.outputTape + 1)) by omega,
    evalConfigWithin_add, rawCompile_extract_exact_eval_from, PMF.pure_bind]
  exact halted_eval _ _ rfl _

theorem rawCompile_extract_eval (source : Program) (input : List Bool) (c : Configuration)
    (budget : Nat) (hFits : extractOutputSteps c.inputTape c.outputTape + 1 ≤ budget) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some) [] c).resumeAt (resultEntry source))
      budget = PMF.pure (rawResult source input c) := by
  simpa only [List.append_nil, rawResultFrom_empty] using rawCompile_extract_eval_from source input [] [] c budget hFits

theorem rawResult_outputBits (source : Program) (input : List Bool) (c : Configuration) :
    (rawResult source input c).outputBits = c.outputBits :=
  extractOutputFinish_outputBits (input.reverse.map some) c.inputTape c.outputTape

theorem resultBudget_polynomiallyBounded {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (resultBudget q) :=
  ((PolynomiallyBounded.const 28).mul
    ((((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 2)).add hq)).add (PolynomiallyBounded.const 27)

theorem rawTraceBudget_polynomiallyBounded {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (rawTraceBudget q) :=
  ((((PolynomiallyBounded.const 31).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 42)).add (preparedTraceBudget_polynomiallyBounded hq)).add
      (resultBudget_polynomiallyBounded hq)

/-- Explicit same-input polynomial overhead, valid for every natural-valued
budget function. The target uses `q(m)` at the original input length, never
an unproved value of `q` at a larger subroutine input. -/
theorem rawTraceBudget_bound (q : Nat → Nat) (m : Nat) :
    rawTraceBudget q m ≤ 125 * (m + 1) * (q m + 1) ^ 2 := by
  calc
    rawTraceBudget q m ≤ rawTraceBudget q m +
        (125 * m * (q m) ^ 2 + 108 * (q m) ^ 2 + 216 * m * q m + 165 * q m + 38 * m) :=
      Nat.le_add_right _ _
    _ = 125 * (m + 1) * (q m + 1) ^ 2 := by
      unfold rawTraceBudget preparedTraceBudget resultBudget
      ring

/-- Full returned tape distribution of the guarded source call. The
continuation has not yet run in this invocation evaluator. -/
theorem rawCompile_return_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalReturnWithin (rawCompile source) (resultEntry source)
      ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
        (preparedSource input)).rebasePc 87) (preparedTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput c).resumeAt
          (resultEntry source)) := by
  let pre := prepareTapes.asSubroutine 0 87
  let suffix := extractOutput.asSubroutine (resultEntry source) (resultEntry source + 65) ++ [.halt]
  let entry := encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput (preparedSource input)
  have hPre : pre.length = 87 := rfl
  have hPc : entry.pc ≤ (compile source).length := by
    simp [entry, encodeConfiguration, preparedSource, address]
  have hLayout : ∀ pc, pc ≤ (compile source).length → pre.length + pc ≠ resultEntry source := by
    intro pc hpc
    rw [hPre]
    dsimp [resultEntry]
    omega
  have h := Program.evalReturnWithin_configuration_eq_of_halted pre (compile source) suffix
    (resultEntry source) hLayout entry hPc rfl (preparedTraceBudget q input.length)
    (compile_prepared_all_branches_halted source input q halts (input.reverse.map some ++ beforeInput) beforeOutput)
  change evalReturnWithin (rawCompile source) (resultEntry source)
    ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
      (preparedSource input)).rebasePc 87) (preparedTraceBudget q input.length) =
      (evalConfigWithin (compile source) entry (preparedTraceBudget q input.length)).map
        (fun c => c.resumeAt (resultEntry source)) at h
  rw [compile_prepared_eval source input q halts (input.reverse.map some ++ beforeInput) beforeOutput, PMF.map_comp] at h
  exact h

theorem rawCompile_return_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalReturnWithin (rawCompile source) (resultEntry source)
      ((encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87) (preparedTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (encodeConfiguration source.length (input.reverse.map some) [] c).resumeAt
          (resultEntry source)) := by
  simpa only [List.append_nil, rawResultFrom_empty] using rawCompile_return_eval_from source input [] [] q halts

private theorem resultBudget_fits (source : Program) (input : List Bool) (q : Nat → Nat)
    (c : Configuration)
    (hc : c ∈ (evalConfigWithin source (preparedSource input) (q input.length)).support) :
    extractOutputSteps c.inputTape c.outputTape + 1 ≤ resultBudget q input.length := by
  have hRun := (mem_support_evalConfigWithin_iff _ _ _ _).mp hc
  have hStorage := sourceStorage_le_of_padded_run hRun
  have hInitial := preparedSource_sourceStorage_le input
  have hExtract := extractOutputSteps_le c.inputTape c.outputTape
  simp only [resultBudget, sourceStorage] at *
  omega

/-- Ordinary execution includes the output continuation, even for branches
that return early. The common budget charges it in full and retains the
complete resulting configuration distribution across every random branch. -/
theorem rawCompile_call_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
        (preparedSource input)).rebasePc 87)
      (preparedTraceBudget q input.length + resultBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map (rawResultFrom source input beforeInput beforeOutput) := by
  have hAfter := evalConfigWithin_after_return (rawCompile source) (resultEntry source)
    ((encodeConfiguration source.length (input.reverse.map some ++ beforeInput) beforeOutput
      (preparedSource input)).rebasePc 87)
    (preparedTraceBudget q input.length) (resultBudget q input.length) id (by
      intro d hd _hPc extra
      rw [rawCompile_return_eval_from source input beforeInput beforeOutput q halts, PMF.mem_support_map_iff] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      have hFits := resultBudget_fits source input q c hc
      rw [rawCompile_extract_eval_from source input beforeInput beforeOutput c _ (by omega),
        rawCompile_extract_eval_from source input beforeInput beforeOutput c _ hFits])
  simp only [PMF.map_id] at hAfter
  rw [hAfter, rawCompile_return_eval_from source input beforeInput beforeOutput q halts, PMF.bind_map]
  change (evalConfigWithin source (preparedSource input) (q input.length)).bind _ =
    (evalConfigWithin source (preparedSource input) (q input.length)).bind
      (fun c => PMF.pure (rawResultFrom source input beforeInput beforeOutput c))
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  exact rawCompile_extract_eval_from source input beforeInput beforeOutput c _ (resultBudget_fits source input q c hc)

theorem rawCompile_call_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompile source)
      ((encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87)
      (preparedTraceBudget q input.length + resultBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map (rawResult source input) := by
  simpa only [List.append_nil, rawResultFrom_empty] using rawCompile_call_eval_from source input [] [] q halts

/-- Probability correctness of the entire actual code, from ordinary raw
input to a halted raw output configuration. Tape preparation, source
simulation and result extraction all have charged operational transitions. -/
theorem rawCompile_configuration_eval_from (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompile source) (packInputStart beforeInput beforeOutput input) (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map (rawResultFrom source input beforeInput beforeOutput) := by
  rw [rawTraceBudget, show 31 * input.length + 42 + preparedTraceBudget q input.length +
      resultBudget q input.length = (31 * input.length + 42) +
        (preparedTraceBudget q input.length + resultBudget q input.length) by omega,
    evalConfigWithin_add, rawCompile_prepare_eval_from, PMF.pure_bind,
    rawCompile_call_eval_from source input beforeInput beforeOutput q halts]

theorem rawCompile_configuration_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompile source) (Configuration.initial input) (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map (rawResult source input) := by
  have h := rawCompile_configuration_eval_from source input [] [] q halts
  have hInitial : packInputStart [] [] input = Configuration.initial input := by cases input <;> rfl
  rw [hInitial] at h
  simpa only [List.append_nil, rawResultFrom_empty] using h

/-- Every source random branch reaches a halted result while retaining the
caller-owned prefixes. The native bound is independent of prefix length,
because the compiled source cannot traverse the guarded outer region. -/
theorem rawCompile_haltsFrom (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    ∀ finish, PaddedRunsFor (rawCompile source)
      (packInputStart beforeInput beforeOutput input) finish (rawTraceBudget q input.length) →
      finish.halted = true := by
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [rawCompile_configuration_eval_from source input beforeInput beforeOutput q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, rfl⟩ := hMem
  rfl

/-- A real raw-input call embedded in any caller. The full result tapes are
returned to the continuation; arbitrary source randomness is retained.
This theorem does not prepare the raw call's initial tapes for free. -/
theorem rawCompile_withSubroutine_return_eval
    (pre suffix : Program) (returnPc : Nat) (source : Program)
    (hLayout : ∀ pc, pc ≤ (rawCompile source).length → pre.length + pc ≠ returnPc)
    (input : List Bool) (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalReturnWithin (Program.withSubroutine pre (rawCompile source) suffix returnPc) returnPc
      ((packInputStart beforeInput beforeOutput input).rebasePc pre.length)
      (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (rawResultFrom source input beforeInput beforeOutput c).resumeAt returnPc) := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre (rawCompile source) suffix
    returnPc hLayout (packInputStart beforeInput beforeOutput input)
    (by simp [packInputStart]) rfl (rawTraceBudget q input.length)
    (rawCompile_haltsFrom source input beforeInput beforeOutput q halts),
    rawCompile_configuration_eval_from source input beforeInput beforeOutput q halts, PMF.map_comp]
  rfl

/-- The raw output lies immediately to the left of the head, followed by
the untouched saved caller data. Input scratch storage remains explicit. -/
theorem rawResultFrom_preserves_saved_data (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) :
    (rawResultFrom source input beforeInput beforeOutput c).inputTape =
        (extractToScratchFinish (input.reverse.map some ++ beforeInput) beforeOutput
          c.inputTape c.outputTape).inputTape ∧
      (rawResultFrom source input beforeInput beforeOutput c).outputTape.left.drop
        c.outputBits.length = beforeOutput :=
  extractOutputFinish_preserves_saved_data (input.reverse.map some ++ beforeInput)
    beforeOutput c.inputTape c.outputTape

theorem rawCompile_haltsWithin (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    HaltsWithin (rawCompile source) input (rawTraceBudget q input.length) := by
  intro final run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [rawCompile_configuration_eval source input q halts, PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, rfl⟩ := hMem
  rfl

theorem rawCompile_polynomialTime (source : Program) (h : PolynomialTime source) :
    PolynomialTime (rawCompile source) := by
  obtain ⟨q, hq, halts⟩ := h
  exact ⟨rawTraceBudget q, rawTraceBudget_polynomiallyBounded hq,
    fun input => rawCompile_haltsWithin source input q (halts input)⟩

/-- The bounded output evaluator of the complete compiled code equals the
original machine's output distribution, with the same original-input source
budget `q(m)`. No monotonicity of `q` or `q` at a longer input is assumed. -/
theorem rawCompile_evalWithin (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalWithin (rawCompile source) input (rawTraceBudget q input.length) =
      evalWithin source input (q input.length) := by
  change (evalConfigWithin (rawCompile source) (Configuration.initial input)
    (rawTraceBudget q input.length)).map (fun c => if c.halted then some c.outputBits else none) = _
  rw [rawCompile_configuration_eval source input q halts, PMF.map_comp,
    ← preparedSource_evalOutput source input (q input.length)]
  change (evalConfigWithin source (preparedSource input) (q input.length)).bind _ =
    (evalConfigWithin source (preparedSource input) (q input.length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hcHalt := preparedSource_all_branches_halted source input _ halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hRawHalt : (rawResult source input c).halted = true := rfl
  simp only [Function.comp_def, hRawHalt, hcHalt, ↓reduceIte, rawResult_outputBits]

end Machine.GuardedCompiler
