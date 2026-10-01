import Foundation.Machine.GuessInputPreparation
import Foundation.Machine.OppositeCall

namespace Machine.GuardedCompiler

/-- Rewind the already assembled request on the physical output tape and
invoke the actual guarded source program. Its raw reply is returned on the
physical input tape. This stage does not yet decode or compare the guess. -/
def storedGuessCallCompile (source : Program) : Program :=
  let pre := rewindBitstring.swapTapes.asSubroutine 0 5
  Program.withSubroutine pre (rawCompileOpposite source) [.halt]
    (pre.length + (rawCompileOpposite source).length + 1)

def storedGuessCallStart (savedInput savedOutput : List (Option Bool))
    (request : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { left := savedInput, right := List.replicate blanks none },
    outputTape := { left := request.reverse.map some ++ none :: savedOutput } }

def storedGuessCallTraceBudget (q : Nat → Nat) (request : List Bool) : Nat :=
  (2*request.length + 4) + rawTraceBudget q request.length + 1

private def storedGuessCallReady (savedInput savedOutput : List (Option Bool))
    (request : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { left := savedInput, right := List.replicate blanks none },
    outputTape := ({ left := savedOutput, right := request.map some ++ [none] } : Tape).moveRight }

private theorem storedGuessCallReady_equivalent (savedInput savedOutput : List (Option Bool))
    (request : List Bool) (blanks : Nat) :
    (storedGuessCallReady savedInput savedOutput request blanks).Equivalent
      (packInputStart (none :: savedOutput) savedInput request).swapTapes := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    simp [storedGuessCallReady, Configuration.swapTapes, packInputStart]
  · cases request with
    | nil =>
        refine ⟨rfl, fun _ => rfl, fun _ => rfl⟩
    | cons bit bits =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        simp only [storedGuessCallReady, Configuration.swapTapes, packInputStart,
          List.map_cons, Tape.moveRight, Tape.ofBits, List.cons_append]
        by_cases h : i < bits.length
        · rw [List.getD_append _ _ _ _ (by simpa using h)]
        · have hle : bits.length ≤ i := by omega
          have hNone : (bits.map some).getD i none = none :=
            List.getD_eq_default _ _ (by simpa using hle)
          rw [List.getD_append_right _ _ _ _ (by simpa using hle), hNone]
          simp

private theorem storedGuessReady_eval {α : Type*} (source : Program)
    (savedInput savedOutput : List (Option Bool)) (request : List Bool) (blanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α) (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (rawCompileOpposite source)
      (storedGuessCallReady savedInput savedOutput request blanks)
      (rawTraceBudget q request.length)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe (rawResultFrom source request (none :: savedOutput) savedInput c).swapTapes) := by
  rw [evalConfigWithin_map_eq_of_equivalent (rawCompileOpposite source) _ _
    (storedGuessCallReady_equivalent savedInput savedOutput request blanks)
    (rawTraceBudget q request.length) observe hObserve]
  have h := congrArg (fun law : PMF Configuration => law.map observe)
    (rawCompileOpposite_configuration_eval source request (none :: savedOutput) savedInput q halts)
  simpa only [PMF.map_comp, Function.comp_def] using h

private theorem storedGuessReady_halts (source : Program)
    (savedInput savedOutput : List (Option Bool)) (request : List Bool) (blanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (rawCompileOpposite source)
      (storedGuessCallReady savedInput savedOutput request blanks) finish
      (rawTraceBudget q request.length)) : finish.halted = true := by
  have hm : finish.halted ∈
      ((evalConfigWithin (rawCompileOpposite source)
        (storedGuessCallReady savedInput savedOutput request blanks)
        (rawTraceBudget q request.length)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [storedGuessReady_eval source savedInput savedOutput request blanks q halts
    Configuration.halted (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hm
  obtain ⟨c, _hc, heq⟩ := hm
  exact heq.symm

/-- Probability law for real source execution after charged rewind of the
retained request. All source random branches are preserved. Observations
must depend on tape cells rather than redundant represented outer blanks. -/
theorem storedGuessCallCompile_evalObservation {α : Type*} (source : Program)
    (savedInput savedOutput : List (Option Bool)) (request : List Bool) (blanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α) (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (storedGuessCallCompile source)
      (storedGuessCallStart savedInput savedOutput request blanks)
      (storedGuessCallTraceBudget q request)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe { (rawResultFrom source request (none :: savedOutput) savedInput c).swapTapes with
          pc := 5 + (rawCompileOpposite source).length + 1, halted := true }) := by
  let pre := rewindBitstring.swapTapes.asSubroutine 0 5
  let ready := storedGuessCallReady savedInput savedOutput request blanks
  let final : Configuration → Configuration := fun c =>
    { c with pc := 5 + (rawCompileOpposite source).length + 1, halted := true }
  have hPre : pre.length = 5 := by simp [pre, Program.asSubroutine_length, Program.swapTapes_length, rewindBitstring]
  have hRewind := (rewindScratch_runs_from savedOutput request none []
    { left := savedInput, right := List.replicate blanks none }).swapTapes.evalConfigWithin_withSubroutine_halted_of_closed
    [] rewindBitstring.swapTapes ((rawCompileOpposite source).asSubroutine 5 (5 + (rawCompileOpposite source).length + 1) ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
    (by intro tape; cases tape <;> simp [rewindBitstring, Program.swapTapes, Instruction.swapTapes])
  have hProgram : Program.withSubroutine [] rewindBitstring.swapTapes
      ((rawCompileOpposite source).asSubroutine 5 (5 + (rawCompileOpposite source).length + 1) ++ [.halt]) 5 =
      storedGuessCallCompile source := by
    simp [storedGuessCallCompile, Program.withSubroutine, hPre, pre, List.append_assoc]
  rw [hProgram] at hRewind
  change evalConfigWithin (storedGuessCallCompile source)
    (storedGuessCallStart savedInput savedOutput request blanks) (2*request.length + 4) =
    PMF.pure (ready.rebasePc 5) at hRewind
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (rawCompileOpposite source) ready
    (by change 0 ≤ (rawCompileOpposite source).length; exact Nat.zero_le _) rfl
    (rawTraceBudget q request.length) (storedGuessReady_halts source savedInput savedOutput request blanks q halts)
  change evalConfigWithin (storedGuessCallCompile source) (ready.rebasePc pre.length)
    (rawTraceBudget q request.length + 1) =
    (evalConfigWithin (rawCompileOpposite source) ready (rawTraceBudget q request.length)).map final at hCall
  rw [hPre] at hCall
  have hRaw := storedGuessReady_eval source savedInput savedOutput request blanks q halts
    (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (5 + (rawCompileOpposite source).length + 1)).withHalted true))
  rw [storedGuessCallTraceBudget, Nat.add_assoc, evalConfigWithin_add, hRewind,
    PMF.pure_bind, hCall, PMF.map_comp]
  exact hRaw

/-- Observe only the actually copied raw reply and halt status. Removing
saved bits is mathematical observation; this is not an uncharged decoder or
cleanup instruction, and it does not yet compare the native challenge. -/
theorem storedGuessCallCompile_evalRawReply (source : Program)
    (savedInput savedOutput : List (Option Bool)) (request : List Bool) (blanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length)) :
    (evalConfigWithin (storedGuessCallCompile source)
      (storedGuessCallStart savedInput savedOutput request blanks)
      (storedGuessCallTraceBudget q request)).map
        (fun c => (c.halted, c.inputTape.bits.drop (savedInput.reverse.filterMap id).length)) =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => (true, c.outputBits)) := by
  rw [storedGuessCallCompile_evalObservation source savedInput savedOutput request blanks q halts
    (fun c => (c.halted, c.inputTape.bits.drop (savedInput.reverse.filterMap id).length)) (by
      intro c d h
      exact congrArg₂ Prod.mk h.2.1 (congrArg (fun bits => bits.drop (savedInput.reverse.filterMap id).length) h.2.2.1.bits))]
  apply congrArg (fun f => (evalConfigWithin source (preparedSource request) (q request.length)).map f)
  funext c
  change (true, ((rawResultFrom source request (none :: savedOutput) savedInput c).swapTapes).inputTape.bits.drop
    (savedInput.reverse.filterMap id).length) = _
  rw [rawCompileOpposite_result_bits]
  simp

/-- The source-call entry is precisely the full native input constructor's
return. The new source sees only this assembled request, while the body copy,
all five earlier blocks and the other tape's caller scratch stay guarded. -/
theorem prepareGuessInputFinish_call_layout (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) :
    let body := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)
    let publicBits := encodeSecurityParameter n ++ frame instanceBits
    let original := publicBits ++ true :: guessInputTupleTail first second last
    let savedInput := body.reverse.map some ++ none :: product.reverse.map some ++
      none :: selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let savedOutput := none :: body.reverse.map some ++ none :: beforeOutput
    (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).resumeAt 0 =
      storedGuessCallStart savedInput savedOutput (publicBits ++ frame body) (padding - 1 - body.length) := by
  dsimp only
  simp [prepareGuessInputFinish, prepareGuessRequestFinish, frameSavedMessageFinish,
    storedGuessCallStart, Configuration.resumeAt, List.reverse_append, List.map_append, List.append_assoc]

theorem storedGuessCallCompile_haltsFrom (source : Program)
    (savedInput savedOutput : List (Option Bool)) (request : List Bool) (blanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (storedGuessCallCompile source)
      (storedGuessCallStart savedInput savedOutput request blanks) finish
      (storedGuessCallTraceBudget q request)) : finish.halted = true := by
  have hm : finish.halted ∈
      ((evalConfigWithin (storedGuessCallCompile source)
        (storedGuessCallStart savedInput savedOutput request blanks)
        (storedGuessCallTraceBudget q request)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [storedGuessCallCompile_evalObservation source savedInput savedOutput request blanks q halts
    Configuration.halted (fun _ _ h => h.2.1), PMF.mem_support_map_iff] at hm
  obtain ⟨c, _hc, heq⟩ := hm
  exact heq.symm

theorem storedGuessCallCompile_length (source : Program) :
    (storedGuessCallCompile source).length = 68*source.length + 162 := by
  simp [storedGuessCallCompile, Program.withSubroutine, Program.asSubroutine_length,
    Program.swapTapes_length, rawCompileOpposite_length, show rewindBitstring.length = 4 from rfl]
  omega

theorem storedGuessCallTraceBudget_bound (q : Nat → Nat) (request : List Bool) :
    storedGuessCallTraceBudget q request ≤ 150*(request.length + 1)*(q request.length + 1)^2 := by
  have hRaw := rawTraceBudget_bound q request.length
  have hPositive : 1 ≤ (q request.length + 1)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [storedGuessCallTraceBudget]
  nlinarith

end Machine.GuardedCompiler
