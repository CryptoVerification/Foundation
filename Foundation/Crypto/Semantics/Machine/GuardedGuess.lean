import Foundation.Crypto.Semantics.Machine.GuessPreparation

namespace Machine.GuardedCompiler

/-- Relative entry of the native guess cleanup after the guarded source's
explicit return jump. This address is determined solely by finite source code. -/
def guessEntry (source : Program) : Nat := (rawCompile source).length + 1

/-- One actual source call followed by native guess cleanup and comparison.
The caller must supply the encoded guess request on the input tape and a
previously sampled challenge behind the output head. This is the final stage
of a simulator, not an implementation of its choose/arithmetic stages. -/
def guessCompile (source : Program) : Program :=
  Program.withSubroutine [] (rawCompile source)
    (finishCopiedGuess.asSubroutine (guessEntry source) (guessEntry source + 39) ++ [.halt])
    (guessEntry source)

theorem guessCompile_length (source : Program) :
    (guessCompile source).length = 68 * source.length + 196 := by
  simp only [guessCompile, Program.withSubroutine, List.length_nil, List.nil_append,
    List.length_append, Program.asSubroutine_length, List.length_singleton,
    show finishCopiedGuess.length = 38 from rfl, rawCompile_length]

def guessStageBudget (q : Nat → Nat) (m : Nat) : Nat := 5 * (2 * m + 2 + q m) + 21

def guessTraceBudget (q : Nat → Nat) (m : Nat) : Nat :=
  rawTraceBudget q m + (guessStageBudget q m + 1)

theorem guessTraceBudget_polynomiallyBounded {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (guessTraceBudget q) :=
  (rawTraceBudget_polynomiallyBounded hq).add
    ((((PolynomiallyBounded.const 5).mul
      ((((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
        (PolynomiallyBounded.const 2)).add hq)).add
          (PolynomiallyBounded.const 21)).add (PolynomiallyBounded.const 1))

/-- Same-original-input quantitative bound for source execution, physical
output cleanup, tagged decoding, bit comparison, and the final caller halt. -/
theorem guessTraceBudget_bound (q : Nat → Nat) (m : Nat) :
    guessTraceBudget q m ≤ 200 * (m + 1) * (q m + 1) ^ 2 := by
  calc
    guessTraceBudget q m ≤ guessTraceBudget q m +
        (200 * m * (q m) ^ 2 + 183 * (q m) ^ 2 + 366 * m * q m +
          310 * q m + 103 * m + 43) := Nat.le_add_right _ _
    _ = _ := by unfold guessTraceBudget guessStageBudget rawTraceBudget preparedTraceBudget resultBudget; ring

private theorem guessCompile_cleanup_layout (source : Program) :
    guessCompile source = Program.withSubroutine
      ((rawCompile source).asSubroutine 0 (guessEntry source)) finishCopiedGuess [.halt]
      (guessEntry source + 39) := by
  simp only [guessCompile, Program.withSubroutine, Program.asSubroutine_length,
    List.length_nil, List.nil_append, guessEntry, List.append_assoc]

private theorem output_size (source : Program) (input : List Bool) (q : Nat → Nat)
    (c : Configuration)
    (hc : c ∈ (evalConfigWithin source (preparedSource input) (q input.length)).support) :
    c.outputBits.length ≤ 2 * input.length + 2 + q input.length := by
  have hStorage := sourceStorage_le_of_padded_run ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  have hInitial := preparedSource_sourceStorage_le input
  have hBits := Tape.bits_length_le_cells c.outputTape
  simp only [Configuration.outputBits, sourceStorage] at *
  omega

/-- Probability semantics from the actual call fixture. Arbitrary source
outputs and every random source branch are handled. The challenge and saved
input data remain outside the source's guarded logical tapes. -/
theorem guessCompile_evalResult (source : Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    (evalConfigWithin (guessCompile source) (packInputStart beforeInput [some challenge] input)
      (guessTraceBudget q input.length)).map (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (true, [taggedGuessValue c.outputBits == challenge])) := by
  let pre := (rawCompile source).asSubroutine 0 (guessEntry source)
  have hPre : pre.length = guessEntry source := by simp [pre, guessEntry]
  have hRaw := rawCompile_withSubroutine_return_eval []
    (finishCopiedGuess.asSubroutine (guessEntry source) (guessEntry source + 39) ++ [.halt])
    (guessEntry source) source (by intro pc hpc; simp only [List.length_nil, Nat.zero_add, guessEntry]; omega)
    input beforeInput [some challenge] q halts
  change evalReturnWithin (guessCompile source) (guessEntry source)
    (packInputStart beforeInput [some challenge] input) (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (rawResultFrom source input beforeInput [some challenge] c).resumeAt (guessEntry source)) at hRaw
  have hTail (c : Configuration)
      (hc : c ∈ (evalConfigWithin source (preparedSource input) (q input.length)).support) (extra : Nat) :
      (evalConfigWithin (guessCompile source)
        ((rawResultFrom source input beforeInput [some challenge] c).resumeAt (guessEntry source))
        (guessStageBudget q input.length + 1 + extra)).map (fun d => (d.halted, d.outputBits)) =
        PMF.pure (true, [taggedGuessValue c.outputBits == challenge]) := by
    let saved := (encodedRightBits c.inputTape).reverse.map some ++
      (encodeTape (input.reverse.map some ++ beforeInput) c.inputTape).left
    let blanks := 2 * c.outputTape.cells + 2 - c.outputBits.length
    let start := prepareCopiedGuessStart saved [] challenge c.outputBits blanks
    have hSize := output_size source input q c hc
    have hFits : finishCopiedGuessSteps c.outputBits ≤ guessStageBudget q input.length + extra := by
      have h := finishCopiedGuess_steps_le c.outputBits
      dsimp [guessStageBudget]
      omega
    have hHalts := finishCopiedGuess_haltsFrom_of_le saved challenge c.outputBits blanks
      (guessStageBudget q input.length + extra) hFits
    have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre finishCopiedGuess start
      (by change 0 ≤ finishCopiedGuess.length; exact Nat.zero_le _) rfl
      (guessStageBudget q input.length + extra) hHalts
    dsimp only at hCall
    have hLayout : Program.withSubroutine pre finishCopiedGuess [.halt]
        (pre.length + finishCopiedGuess.length + 1) = guessCompile source := by
      rw [hPre, show finishCopiedGuess.length = 38 from rfl]
      change Program.withSubroutine pre finishCopiedGuess [.halt] (guessEntry source + 39) = _
      exact (guessCompile_cleanup_layout source).symm
    rw [hLayout] at hCall
    have hEntry : start.rebasePc pre.length =
        (rawResultFrom source input beforeInput [some challenge] c).resumeAt (guessEntry source) := by
      have h := congrArg (fun d => d.rebasePc (guessEntry source))
        (rawResultFrom_prepareCopiedGuessStart source input beforeInput [] challenge c)
      simpa only [Configuration.resumeAt, Configuration.rebasePc, Nat.zero_add, Nat.add_zero, hPre] using h.symm
    rw [hEntry] at hCall
    rw [show guessStageBudget q input.length + 1 + extra =
      (guessStageBudget q input.length + extra) + 1 by omega, hCall, PMF.map_comp]
    change (evalConfigWithin finishCopiedGuess start (guessStageBudget q input.length + extra)).map
      (fun d => (true, d.outputBits)) = _
    have h := congrArg (fun distribution : PMF (Bool × List Bool) =>
        distribution.map (fun pair => (true, pair.2)))
      (finishCopiedGuess_evalResult_of_le saved challenge c.outputBits blanks
        (guessStageBudget q input.length + extra) hFits)
    simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map] using h
  have hAfter := evalConfigWithin_after_return (guessCompile source) (guessEntry source)
    (packInputStart beforeInput [some challenge] input) (rawTraceBudget q input.length)
    (guessStageBudget q input.length + 1) (fun c => (c.halted, c.outputBits)) (by
      intro d hd _hPc extra
      rw [hRaw, PMF.mem_support_map_iff] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      rw [hTail c hc extra, hTail c hc 0])
  rw [guessTraceBudget, hAfter, hRaw, PMF.bind_map]
  change (evalConfigWithin source (preparedSource input) (q input.length)).bind _ =
    (evalConfigWithin source (preparedSource input) (q input.length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  exact hTail c hc 0

/-- Worst-case native halting on every source random branch from the valid
call fixture. No average-case or selected-branch running time is used. -/
theorem guessCompile_haltsFrom (source : Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    ∀ c, PaddedRunsFor (guessCompile source)
      (packInputStart beforeInput [some challenge] input) c (guessTraceBudget q input.length) →
      c.halted = true := by
  intro c run
  have hMem : (c.halted, c.outputBits) ∈ ((evalConfigWithin (guessCompile source)
      (packInputStart beforeInput [some challenge] input) (guessTraceBudget q input.length)).map
        (fun c => (c.halted, c.outputBits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [guessCompile_evalResult source input beforeInput challenge q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨d, _hd, hEq⟩ := hMem
  exact (congrArg Prod.fst hEq).symm

/-- The output distribution of the compiled final stage is precisely the
source's raw guess-output distribution interpreted and compared with the
stored challenge. Timeout handling remains identical to the source adapter;
the supplied stopping premise ensures there is actually no timeout mass. -/
theorem guessCompile_evalOutput (source : Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    (evalConfigWithin (guessCompile source) (packInputStart beforeInput [some challenge] input)
      (guessTraceBudget q input.length)).map Configuration.outputBits =
      (evalWithin source input (q input.length)).map
        (fun output => [(match output with | some bits => taggedGuessValue bits | none => false) == challenge]) := by
  have h := congrArg (fun distribution : PMF (Bool × List Bool) => distribution.map Prod.snd)
    (guessCompile_evalResult source input beforeInput challenge q halts)
  simp only [PMF.map_comp, Function.comp_def] at h
  rw [h, ← preparedSource_evalOutput source input (q input.length), PMF.map_comp]
  change (evalConfigWithin source (preparedSource input) (q input.length)).bind _ =
    (evalConfigWithin source (preparedSource input) (q input.length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hHalted := preparedSource_all_branches_halted source input _ halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  simp only [Function.comp_def, hHalted, ↓reduceIte]

end Machine.GuardedCompiler
