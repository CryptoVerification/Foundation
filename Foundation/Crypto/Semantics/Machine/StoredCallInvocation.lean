import Foundation.Crypto.Semantics.Machine.StoredCallPreparation

namespace Machine.GuardedCompiler

/-- Fixed finite code: prepare the two actual tapes, run the supplied fixed
source program through the guarded compiler, and execute a final halt. -/
def storedCallCompile (source : Program) : Program :=
  let pre := prepareStoredCall.asSubroutine 0 31
  let call := rawCompileOpposite source
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

def storedCallTraceBudget (q : Nat → Nat) (first second third fourth request : List Bool) : Nat :=
  prepareStoredCallSteps first second third fourth request + rawTraceBudget q request.length + 1

/-- Preparation has linear cost in the four retained blocks and assembled
request. Guarded source execution uses its budget at the actual request
length. A larger stored prefix does not require monotonicity of that budget. -/
theorem storedCallTraceBudget_bound (q : Nat → Nat)
    (first second third fourth request : List Bool) :
    storedCallTraceBudget q first second third fourth request ≤
      150 * (first.length + second.length + third.length + fourth.length + request.length + 1) *
        (q request.length + 1)^2 := by
  let t := (q request.length + 1)^2
  have hPositive : 1 ≤ t := Nat.one_le_pow _ _ (by omega)
  have hRaw := rawTraceBudget_bound q request.length
  change rawTraceBudget q request.length ≤ 125 * (request.length + 1) * t at hRaw
  change storedCallTraceBudget q first second third fourth request ≤
    150 * (first.length + second.length + third.length + fourth.length + request.length + 1) * t
  dsimp only [storedCallTraceBudget, prepareStoredCallSteps]
  nlinarith

theorem storedCallCompile_length (source : Program) :
    (storedCallCompile source).length = 68 * source.length + 188 := by
  simp [storedCallCompile, Program.withSubroutine, rawCompileOpposite_length,
    Program.asSubroutine_length, show prepareStoredCall.length = 30 from rfl]
  omega

private theorem storedCallCompile_layout (source : Program) :
    Program.withSubroutine [] prepareStoredCall
      ((rawCompileOpposite source).asSubroutine 31 (31 + (rawCompileOpposite source).length + 1) ++ [.halt]) 31 =
      storedCallCompile source := by
  simp [storedCallCompile, Program.withSubroutine, Program.asSubroutine_length,
    show prepareStoredCall.length = 30 from rfl, List.append_assoc]

/-- Entire native source-call law. The preparation in this finite program
is charged before invoking the certificate; no stored request is reloaded. -/
theorem storedCallCompile_evalObservation {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (storedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedCallTraceBudget q first second third fourth request)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe {
          (rawResultFrom source request (none :: beforeOutput)
            (none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
              none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c).swapTapes
          with pc := 31 + (rawCompileOpposite source).length + 1, halted := true }) := by
  let pre := prepareStoredCall.asSubroutine 0 31
  let start := (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0
  let final : Configuration → Configuration := fun c =>
    { c with pc := 31 + (rawCompileOpposite source).length + 1, halted := true }
  have hPrepare := (prepareStoredCall_runs beforeInput beforeOutput first second third fourth request
      inputBlanks outputBlanks).evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareStoredCall
    ((rawCompileOpposite source).asSubroutine 31 (31 + (rawCompileOpposite source).length + 1) ++ [.halt]) 31
    (by change 0 < 30; decide) rfl rfl prepareStoredCall_control_closed prepareStoredCall_no_randomBit
  rw [storedCallCompile_layout] at hPrepare
  change evalConfigWithin (storedCallCompile source)
    (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
    (prepareStoredCallSteps first second third fourth request) =
      PMF.pure ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (rawCompileOpposite source) start
    (by change 0 ≤ (rawCompileOpposite source).length; exact Nat.zero_le _) rfl
    (rawTraceBudget q request.length)
    (prepareStoredCall_call_haltsFrom source beforeInput beforeOutput first second third fourth request
      inputBlanks outputBlanks q halts)
  change evalConfigWithin (storedCallCompile source) (start.rebasePc pre.length)
    (rawTraceBudget q request.length + 1) =
      (evalConfigWithin (rawCompileOpposite source) start (rawTraceBudget q request.length)).map final at hCall
  have hEntry : start.rebasePc pre.length =
      (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31 := rfl
  rw [hEntry] at hCall
  have hRaw := prepareStoredCall_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (31 + (rawCompileOpposite source).length + 1)).withHalted true))
  rw [storedCallTraceBudget, Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind,
    hCall, PMF.map_comp]
  exact hRaw

/-- Every native random branch halts within the displayed preparation and
source-simulation budget. The request length is the source budget argument. -/
theorem storedCallCompile_haltsFrom (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (storedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      finish (storedCallTraceBudget q first second third fourth request)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (storedCallCompile source)
        (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
        (storedCallTraceBudget q first second third fourth request)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [storedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm

/-- Observe just the newly returned raw source bits. The prefix length here
is an observation of stored caller cells, not a native slicing instruction;
the full returned-state theorem remains available for the next native stage. -/
theorem storedCallCompile_evalResult (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length)) :
    let saved := none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
      none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput
    (evalConfigWithin (storedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedCallTraceBudget q first second third fourth request)).map
        (fun c => (c.halted, c.inputTape.bits.drop (saved.reverse.filterMap id).length)) =
      (evalWithin source request (q request.length)).map
        (fun result => (true, result.getD [])) := by
  dsimp only
  rw [storedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts
    (fun c => (c.halted, c.inputTape.bits.drop
      ((none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput).reverse.filterMap id).length))
    (by intro c d h; exact congrArg₂ Prod.mk h.2.1 (congrArg _ h.2.2.1.bits)),
    ← preparedSource_evalOutput source request (q request.length), PMF.map_comp]
  change (evalConfigWithin source (preparedSource request) (q request.length)).bind _ =
    (evalConfigWithin source (preparedSource request) (q request.length)).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hHalted := preparedSource_all_branches_halted source request _ halts c
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  simp only [Function.comp_def, hHalted, ↓reduceIte]
  change PMF.pure (true,
    ((rawResultFrom source request (none :: beforeOutput)
      (none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c).swapTapes).inputTape.bits.drop
      ((none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput).reverse.filterMap id).length) =
    PMF.pure (true, c.outputBits)
  rw [rawCompileOpposite_result_bits, List.drop_left]

end Machine.GuardedCompiler
