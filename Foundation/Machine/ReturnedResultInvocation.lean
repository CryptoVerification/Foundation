import Foundation.Machine.ReturnedResultFraming

namespace Machine.GuardedCompiler

def returnedFrameEntry (source : Program) : Nat := (rawCompileOpposite source).length + 1

/-- A real opposite-tape source call followed by native result framing.
The result is stored beyond the retained source scratch. This wrapper does
not decode the result or reconstruct any other cryptographic request field. -/
def returnedFrameCompile (source : Program) : Program :=
  Program.withSubroutine [] (rawCompileOpposite source)
    (frameReturnedResult.asSubroutine (returnedFrameEntry source) (returnedFrameEntry source + 33) ++ [.halt])
    (returnedFrameEntry source)

def returnedFrameStageBudget (q : Nat → Nat) (m : Nat) : Nat :=
  15*(2*m + 2 + q m) + 17

def returnedFrameTraceBudget (q : Nat → Nat) (m : Nat) : Nat :=
  rawTraceBudget q m + (returnedFrameStageBudget q m + 1)

/-- Full physical state after the framed result and the actual caller halt.
This specification preserves both source tapes and both caller prefixes. -/
def returnedFrameResult (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (c : Configuration) : Configuration :=
  { frameReturnedResultFinish savedOutput
      (c.outputBits.reverse.map some ++ scratchPrefix (input.reverse.map some ++ beforeInput) c.inputTape)
      (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) c.outputBits 0
    with pc := returnedFrameEntry source + 33 }

theorem returnedFrameCompile_length (source : Program) :
    (returnedFrameCompile source).length = 68*source.length + 190 := by
  simp [returnedFrameCompile, Program.withSubroutine, Program.asSubroutine_length,
    show frameReturnedResult.length = 32 from rfl, rawCompileOpposite_length]

theorem returnedFrameTraceBudget_polynomiallyBounded {q : Nat → Nat}
    (h : PolynomiallyBounded q) : PolynomiallyBounded (returnedFrameTraceBudget q) :=
  (rawTraceBudget_polynomiallyBounded h).add
    ((((PolynomiallyBounded.const 15).mul
      ((((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
        (PolynomiallyBounded.const 2)).add h)).add
          (PolynomiallyBounded.const 17)).add (PolynomiallyBounded.const 1))

theorem returnedFrameTraceBudget_bound (q : Nat → Nat) (m : Nat) :
    returnedFrameTraceBudget q m ≤ 200*(m+1)*(q m + 1)^2 := by
  have hRaw := rawTraceBudget_bound q m
  have hPositive : 1 ≤ (q m + 1)^2 := Nat.one_le_pow _ _ (by omega)
  have hTime : q m ≤ (q m + 1)^2 := by nlinarith
  dsimp only [returnedFrameTraceBudget, returnedFrameStageBudget]
  nlinarith

private theorem compiled_layout (source : Program) :
    returnedFrameCompile source = Program.withSubroutine
      ((rawCompileOpposite source).asSubroutine 0 (returnedFrameEntry source)) frameReturnedResult [.halt]
      (returnedFrameEntry source + 33) := by
  simp [returnedFrameCompile, Program.withSubroutine, returnedFrameEntry,
    Program.asSubroutine_length, List.append_assoc]

private theorem result_halted (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (c : Configuration) :
    (returnedFrameResult source input beforeInput savedOutput c).halted = true := rfl

private theorem eval_halted (program : Program) (c : Configuration)
    (h : c.halted = true) (extra : Nat) : evalConfigWithin program c extra = PMF.pure c := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem framed_result_exact (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (c : Configuration) :
    evalConfigWithin (returnedFrameCompile source)
      (((rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt
        (returnedFrameEntry source))
      (frameReturnedResultSteps c.outputBits + 1) =
      PMF.pure (returnedFrameResult source input beforeInput savedOutput c) := by
  let pre := (rawCompileOpposite source).asSubroutine 0 (returnedFrameEntry source)
  have hPre : pre.length = returnedFrameEntry source := by
    simp [pre, Program.asSubroutine_length, returnedFrameEntry]
  let saved := c.outputBits.reverse.map some ++ scratchPrefix (input.reverse.map some ++ beforeInput) c.inputTape
  let tail : List (Option Bool) := List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none
  have hFrame := (frameReturnedResult_runs savedOutput saved tail c.outputBits 0).evalConfigWithin_withSubroutine_halted_of_closed
    pre frameReturnedResult [.halt] (returnedFrameEntry source + 33)
    (by change 0 < 32; decide) rfl rfl frameReturnedResult_control_closed frameReturnedResult_no_randomBit
  rw [← compiled_layout] at hFrame
  have hStart : (frameReturnedResultStart savedOutput saved tail c.outputBits 0).rebasePc pre.length =
      (((rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt
        (returnedFrameEntry source)) := by
    rw [hPre]
    change (frameReturnedResultStart savedOutput
      (c.outputBits.reverse.map some ++ scratchPrefix (input.reverse.map some ++ beforeInput) c.inputTape)
      (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) c.outputBits 0).rebasePc
      (returnedFrameEntry source) = _
    rw [← rawResultFrom_frameReturnedResultStart source input beforeInput savedOutput c]
    simp only [Configuration.rebasePc, Configuration.resumeAt, Nat.add_zero]
  rw [hStart] at hFrame
  have hHalt : (returnedFrameCompile source)[returnedFrameEntry source + 33]? = some .halt := by
    rw [compiled_layout]
    have h := Program.withSubroutine_getElem?_suffix pre frameReturnedResult [.halt]
      (returnedFrameEntry source + 33) 0
    simpa [hPre, show frameReturnedResult.length = 32 from rfl] using h
  rw [evalConfigWithin_add, hFrame, PMF.pure_bind]
  simp [evalConfigWithin, stepPMF, next, Configuration.resumeAt, hHalt, Instruction.next,
    returnedFrameResult, frameReturnedResultFinish, saved, tail]

private theorem framed_result_padded (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (q : Nat → Nat)
    (c : Configuration)
    (hc : c ∈ (evalConfigWithin source (preparedSource input) (q input.length)).support) (extra : Nat) :
    evalConfigWithin (returnedFrameCompile source)
      (((rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt
        (returnedFrameEntry source))
      (returnedFrameStageBudget q input.length + 1 + extra) =
      PMF.pure (returnedFrameResult source input beforeInput savedOutput c) := by
  have hStorage := sourceStorage_le_of_padded_run ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hInitial := preparedSource_sourceStorage_le input
  have hBits := Tape.bits_length_le_cells c.outputTape
  have hCost := frameReturnedResult_steps_le c.outputBits
  have hFits : frameReturnedResultSteps c.outputBits + 1 ≤ returnedFrameStageBudget q input.length + 1 + extra := by
    simp only [Configuration.outputBits, sourceStorage, returnedFrameStageBudget] at *
    omega
  rw [show returnedFrameStageBudget q input.length + 1 + extra =
      (frameReturnedResultSteps c.outputBits + 1) +
        (returnedFrameStageBudget q input.length + 1 + extra - (frameReturnedResultSteps c.outputBits + 1)) by omega,
    evalConfigWithin_add, framed_result_exact, PMF.pure_bind]
  exact eval_halted _ _ (result_halted _ _ _ _ _) _

/-- Complete probability law for an actual source call and subsequent
native frame construction, including every source random branch. Early
return executes the continuation immediately; padding occurs only after
the final caller halt. -/
theorem returnedFrameCompile_eval (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (returnedFrameCompile source)
      (packInputStart beforeInput (none :: savedOutput) input).swapTapes
      (returnedFrameTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (returnedFrameResult source input beforeInput savedOutput) := by
  have hReturn := Program.evalReturnWithin_configuration_eq_of_halted [] (rawCompileOpposite source)
    (frameReturnedResult.asSubroutine (returnedFrameEntry source) (returnedFrameEntry source + 33) ++ [.halt])
    (returnedFrameEntry source) (by intro pc hpc; simp only [List.length_nil, Nat.zero_add, returnedFrameEntry]; omega)
    (packInputStart beforeInput (none :: savedOutput) input).swapTapes
    (by simp [packInputStart, Configuration.swapTapes]) rfl (rawTraceBudget q input.length)
    (rawCompileOpposite_haltsFrom source input beforeInput (none :: savedOutput) q halts)
  change evalReturnWithin (returnedFrameCompile source) (returnedFrameEntry source)
    (packInputStart beforeInput (none :: savedOutput) input).swapTapes (rawTraceBudget q input.length) = _ at hReturn
  rw [rawCompileOpposite_configuration_eval source input beforeInput (none :: savedOutput) q halts,
    PMF.map_comp] at hReturn
  change evalReturnWithin (returnedFrameCompile source) (returnedFrameEntry source)
    (packInputStart beforeInput (none :: savedOutput) input).swapTapes (rawTraceBudget q input.length) =
    (evalConfigWithin source (preparedSource input) (q input.length)).map
      (fun c => ((rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt
        (returnedFrameEntry source)) at hReturn
  have hContinue := evalConfigWithin_after_return (returnedFrameCompile source) (returnedFrameEntry source)
    (packInputStart beforeInput (none :: savedOutput) input).swapTapes
    (rawTraceBudget q input.length) (returnedFrameStageBudget q input.length + 1) id (by
      intro d hd _hPc extra
      rw [hReturn, PMF.mem_support_map_iff] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      simp only [PMF.map_id]
      rw [framed_result_padded source input beforeInput savedOutput q c hc extra,
        ← Nat.add_zero (returnedFrameStageBudget q input.length + 1),
        framed_result_padded source input beforeInput savedOutput q c hc 0])
  simp only [PMF.map_id] at hContinue
  rw [returnedFrameTraceBudget, hContinue, hReturn, PMF.bind_map]
  change (evalConfigWithin source (preparedSource input) (q input.length)).bind _ =
    (evalConfigWithin source (preparedSource input) (q input.length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  exact framed_result_padded source input beforeInput savedOutput q c hc 0

theorem returnedFrameCompile_haltsFrom (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) (finish : Configuration)
    (run : PaddedRunsFor (returnedFrameCompile source)
      (packInputStart beforeInput (none :: savedOutput) input).swapTapes finish
      (returnedFrameTraceBudget q input.length)) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [returnedFrameCompile_eval _ _ _ _ _ halts, PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, rfl⟩ := hMem
  rfl

end Machine.GuardedCompiler
