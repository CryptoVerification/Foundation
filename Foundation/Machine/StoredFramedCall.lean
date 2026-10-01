import Foundation.Machine.StoredCallPreparation
import Foundation.Machine.ReturnedResultInvocation

namespace Machine.GuardedCompiler

/-- Native preparation of the retained caller tapes, followed by the real
source invocation and result framing. No raw request or returned result is
supplied by a fresh initial-configuration operation inside this program. -/
def storedFramedCallCompile (source : Program) : Program :=
  let pre := prepareStoredCall.asSubroutine 0 31
  let call := returnedFrameCompile source
  Program.withSubroutine pre call [.halt] (pre.length + call.length + 1)

def storedFramedCallTraceBudget (q : Nat → Nat) (first second third fourth request : List Bool) : Nat :=
  prepareStoredCallSteps first second third fourth request + returnedFrameTraceBudget q request.length + 1

theorem storedFramedCallCompile_length (source : Program) :
    (storedFramedCallCompile source).length = 68*source.length + 223 := by
  simp [storedFramedCallCompile, Program.withSubroutine, returnedFrameCompile_length,
    Program.asSubroutine_length, show prepareStoredCall.length = 30 from rfl]
  omega

theorem storedFramedCallTraceBudget_bound (q : Nat → Nat)
    (first second third fourth request : List Bool) :
    storedFramedCallTraceBudget q first second third fourth request ≤
      225*(first.length + second.length + third.length + fourth.length + request.length + 1)*
        (q request.length + 1)^2 := by
  have hRaw := returnedFrameTraceBudget_bound q request.length
  have hPositive : 1 ≤ (q request.length + 1)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [storedFramedCallTraceBudget, prepareStoredCallSteps]
  nlinarith

private theorem prepared_framed_eval {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (returnedFrameCompile source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      (returnedFrameTraceBudget q request.length)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe (returnedFrameResult source request (none :: beforeOutput)
          (fourth.reverse.map some ++ none :: third.reverse.map some ++
            none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c)) := by
  rw [evalConfigWithin_map_eq_of_equivalent (returnedFrameCompile source) _ _
    (prepareStoredCall_call_layout beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
    (returnedFrameTraceBudget q request.length) observe hObserve]
  have h := congrArg (fun law : PMF Configuration => law.map observe)
    (returnedFrameCompile_eval source request (none :: beforeOutput)
      (fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) q halts)
  simpa only [List.cons_append, List.append_assoc, PMF.map_comp, Function.comp_def] using h

private theorem prepared_framed_halts (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (returnedFrameCompile source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      finish (returnedFrameTraceBudget q request.length)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (returnedFrameCompile source)
        ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
        (returnedFrameTraceBudget q request.length)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [prepared_framed_eval source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm

private theorem compiled_layout (source : Program) :
    Program.withSubroutine [] prepareStoredCall
      ((returnedFrameCompile source).asSubroutine 31 (31 + (returnedFrameCompile source).length + 1) ++ [.halt]) 31 =
      storedFramedCallCompile source := by
  simp [storedFramedCallCompile, Program.withSubroutine, Program.asSubroutine_length,
    show prepareStoredCall.length = 30 from rfl, List.append_assoc]

/-- Full native preparation, invocation, and framing probability law on the
actual retained tapes. The observation must depend on cells, not redundant
outer blank representation. All three stages consume their own steps. -/
theorem storedFramedCallCompile_evalObservation {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedFramedCallTraceBudget q first second third fourth request)).map observe =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => observe {
          returnedFrameResult source request (none :: beforeOutput)
            (fourth.reverse.map some ++ none :: third.reverse.map some ++
              none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c
          with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }) := by
  let pre := prepareStoredCall.asSubroutine 0 31
  let start := (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0
  let final : Configuration → Configuration := fun c =>
    { c with pc := 31 + (returnedFrameCompile source).length + 1, halted := true }
  have hPrepare := (prepareStoredCall_runs beforeInput beforeOutput first second third fourth request
      inputBlanks outputBlanks).evalConfigWithin_withSubroutine_halted_of_closed
    [] prepareStoredCall
    ((returnedFrameCompile source).asSubroutine 31 (31 + (returnedFrameCompile source).length + 1) ++ [.halt]) 31
    (by change 0 < 30; decide) rfl rfl prepareStoredCall_control_closed prepareStoredCall_no_randomBit
  rw [compiled_layout] at hPrepare
  change evalConfigWithin (storedFramedCallCompile source)
    (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
    (prepareStoredCallSteps first second third fourth request) =
      PMF.pure ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31) at hPrepare
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre (returnedFrameCompile source) start
    (by change 0 ≤ (returnedFrameCompile source).length; exact Nat.zero_le _) rfl
    (returnedFrameTraceBudget q request.length)
    (prepared_framed_halts source beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks q halts)
  change evalConfigWithin (storedFramedCallCompile source) (start.rebasePc pre.length)
    (returnedFrameTraceBudget q request.length + 1) =
      (evalConfigWithin (returnedFrameCompile source) start (returnedFrameTraceBudget q request.length)).map final at hCall
  have hEntry : start.rebasePc pre.length =
      (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 31 := rfl
  rw [hEntry] at hCall
  have hRaw := prepared_framed_eval source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts (fun c => observe (final c)) (by
      intro c d h
      exact hObserve _ _ ((h.withPc (31 + (returnedFrameCompile source).length + 1)).withHalted true))
  rw [storedFramedCallTraceBudget, Nat.add_assoc, evalConfigWithin_add, hPrepare, PMF.pure_bind,
    hCall, PMF.map_comp]
  exact hRaw

theorem storedFramedCallCompile_haltsFrom (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      finish (storedFramedCallTraceBudget q first second third fourth request)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (storedFramedCallCompile source)
        (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
        (storedFramedCallTraceBudget q first second third fourth request)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [storedFramedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm

/-- If the called program returns one canonical result, its frame really
occupies these physical output cells after the whole charged invocation.
Reading cells here is a mathematical observation, not a machine copy opcode.
The full state law above remains available for a native continuation. -/
theorem storedFramedCallCompile_evalFrameCells (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request expected : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (correct : evalWithin source request (q request.length) = PMF.pure (some expected)) :
    (evalConfigWithin (storedFramedCallCompile source)
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (storedFramedCallTraceBudget q first second third fourth request)).map
        (fun c => (c.halted, fun i : Fin (frame expected).length => c.outputTape.left.getD i.val none)) =
      PMF.pure (true, fun i : Fin (frame expected).length =>
        ((frame expected).reverse.map some).getD i.val none) := by
  let observe : Configuration → Bool × (Fin (frame expected).length → Option Bool) := fun c =>
    (c.halted, fun i => c.outputTape.left.getD i.val none)
  have hObserve : ∀ c d, c.Equivalent d → observe c = observe d := by
    intro c d h
    exact congrArg₂ Prod.mk h.2.1 (funext fun i => h.2.2.2.2.1 i.val)
  rw [storedFramedCallCompile_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts observe hObserve]
  have hOutput := (preparedSource_evalOutput source request (q request.length)).trans correct
  let target := (true, fun i : Fin (frame expected).length => ((frame expected).reverse.map some).getD i.val none)
  change (evalConfigWithin source (preparedSource request) (q request.length)).bind _ = PMF.pure target
  calc
    _ = (evalConfigWithin source (preparedSource request) (q request.length)).bind (fun _ => PMF.pure target) := by
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext c hc
      have hHalted := preparedSource_all_branches_halted source request _ halts c
        ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
      have hMem : (if c.halted then some c.outputBits else none) ∈
          ((evalConfigWithin source (preparedSource request) (q request.length)).map
            (fun d => if d.halted then some d.outputBits else none)).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨c, hc, rfl⟩
      rw [hOutput, PMF.mem_support_pure_iff] at hMem
      have hBits : c.outputBits = expected := by simpa only [hHalted, ↓reduceIte, Option.some.injEq] using hMem
      dsimp only [Function.comp_def]
      apply congrArg PMF.pure
      apply Prod.ext
      · rfl
      · funext i
        dsimp only [returnedFrameResult, frameReturnedResultFinish, target]
        rw [hBits]
        exact List.getD_append _ _ _ _ (by simp only [List.length_map, List.length_reverse]; exact i.isLt)
    _ = _ := PMF.bind_const _ _

end Machine.GuardedCompiler
