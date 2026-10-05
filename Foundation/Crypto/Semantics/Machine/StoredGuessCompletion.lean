import Foundation.Crypto.Semantics.Machine.StoredGuessRewind

namespace Machine

/-- Complete native continuation from a stored raw guess: rewind and erase
its parallel copy, locate the actual saved challenge through the known
protocol blocks, validate/compare the guess, clear the remaining scratch,
and return exactly one output bit. Only block counts enter the fixed code. -/
def finishStoredGuess (frontCount backCount : Nat) : Program :=
  let prepare := prepareStoredGuess frontCount
  let pre := prepare.asSubroutine 0 (prepare.length + 1)
  let finish := finishStoredTaggedGuess backCount
  Program.withSubroutine pre finish [.halt] (pre.length + finish.length + 1)

def finishStoredGuessSteps (front back : List (List Bool)) (bits : List Bool) : Nat :=
  prepareStoredGuessSteps front bits + (finishStoredTaggedGuessSteps back bits + 1)

private theorem halted_eval (p : Program) (c : Configuration) (h : c.halted = true) (extra : Nat) :
    evalConfigWithin p c extra = PMF.pure c := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem pair_observe (c d : Configuration) (h : c.Equivalent d) :
    (c.halted, c.outputBits) = (d.halted, d.outputBits) :=
  congrArg₂ Prod.mk h.2.1 h.outputBits

theorem finishStoredGuess_evalResult (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) :
    (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
      (finishStoredGuessSteps front back bits)).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
  let prepare := prepareStoredGuess front.length
  let returnPc := prepare.length + 1
  let pre := prepare.asSubroutine 0 returnPc
  let finish := finishStoredTaggedGuess back.length
  let finalPc := pre.length + finish.length + 1
  let start := prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks
  let prepared := prepareStoredGuessFinish beforeInput boundary front back challenge bits inputBlanks outputBlanks
  let finishStart := prepared.resumeAt 0
  let t₁ := prepareStoredGuessSteps front bits
  let t₂ := finishStoredTaggedGuessSteps back bits
  let observe : Configuration → Bool × List Bool := fun c => (c.halted, c.outputBits)
  have hPre : pre.length = returnPc := by simp [pre, Program.asSubroutine_length, returnPc]
  have hFirstProgram : Program.withSubroutine [] prepare
      (finish.asSubroutine returnPc finalPc ++ [.halt]) returnPc = finishStoredGuess front.length back.length := by
    simp only [finishStoredGuess, Program.withSubroutine, List.length_nil, List.nil_append,
      pre, prepare, finish, finalPc, hPre, returnPc, List.append_assoc]
  have first := Program.evalReturnWithin_configuration_eq_of_halted [] prepare
    (finish.asSubroutine returnPc finalPc ++ [.halt]) returnPc
    (by intro pc hpc; simp only [List.length_nil, Nat.zero_add]; dsimp only [returnPc]; omega)
    start (by change 0 ≤ prepare.length; omega) rfl t₁
    (prepareStoredGuess_haltsFrom beforeInput boundary front back challenge bits inputBlanks outputBlanks)
  rw [hFirstProgram] at first
  have hStartZero : start.rebasePc 0 = start := by
    simp [start, prepareStoredGuessStart, rewindStoredGuessStart, Configuration.rebasePc]
  simp only [List.length_nil] at first
  rw [hStartZero] at first
  change evalReturnWithin (finishStoredGuess front.length back.length) returnPc start t₁ =
    (evalConfigWithin (prepareStoredGuess front.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
      (prepareStoredGuessSteps front bits)).map (fun c => c.resumeAt returnPc) at first
  rw [prepareStoredGuess_eval, PMF.pure_map] at first
  change evalReturnWithin (finishStoredGuess front.length back.length) returnPc start t₁ =
    PMF.pure (prepared.resumeAt returnPc) at first
  have equivalent := prepareStoredGuessFinish_equivalent beforeInput boundary front back challenge bits inputBlanks outputBlanks
  have hFinish : (evalConfigWithin finish finishStart t₂).map observe =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
    rw [evalConfigWithin_map_eq_of_equivalent finish finishStart _ equivalent t₂ observe pair_observe]
    exact finishStoredTaggedGuess_evalResult _ _ _ _
  have hFinishHalts : ∀ c, PaddedRunsFor finish finishStart c t₂ → c.halted = true := by
    intro c run
    have hc : observe c ∈ ((evalConfigWithin finish finishStart t₂).map observe).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hFinish] at hc
    have heq : observe c = (true, [taggedGuessValue bits == challenge]) := by simpa using hc
    exact congrArg Prod.fst heq
  have last := Program.evalConfigWithin_withSubroutine_final_halt pre finish finishStart
    (by change 0 ≤ finish.length; omega) rfl t₂ hFinishHalts
  have hLastProgram : Program.withSubroutine pre finish [.halt] (pre.length + finish.length + 1) =
      finishStoredGuess front.length back.length := rfl
  dsimp only at last
  rw [hLastProgram] at last
  have hEntry : finishStart.rebasePc pre.length = prepared.resumeAt returnPc := by
    simp [finishStart, Configuration.rebasePc, Configuration.resumeAt, hPre]
  rw [hEntry] at last
  have hLastResult : (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepared.resumeAt returnPc) (t₂ + 1)).map observe =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
    rw [last, PMF.map_comp]
    change (evalConfigWithin finish finishStart t₂).bind _ = _
    change (evalConfigWithin finish finishStart t₂).bind _ = _ at hFinish
    rw [← PMF.bindOnSupport_eq_bind] at hFinish ⊢
    convert hFinish using 1
    congr 1
    funext c hc
    have hHalt := hFinishHalts c ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    simp [observe, hHalt, Configuration.outputBits]
  have hCallerHalts : ∀ c ∈ (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepared.resumeAt returnPc) (t₂ + 1)).support, c.halted = true := by
    intro c hc
    have hm : observe c ∈ ((evalConfigWithin (finishStoredGuess front.length back.length)
        (prepared.resumeAt returnPc) (t₂ + 1)).map observe).support := by
      rw [PMF.mem_support_map_iff]; exact ⟨c, hc, rfl⟩
    rw [hLastResult] at hm
    have heq : observe c = (true, [taggedGuessValue bits == challenge]) := by simpa using hm
    exact congrArg Prod.fst heq
  have stable (d : Configuration)
      (hd : d ∈ (evalReturnWithin (finishStoredGuess front.length back.length) returnPc start t₁).support)
      (_hPc : d.pc = returnPc) (extra : Nat) :
      (evalConfigWithin (finishStoredGuess front.length back.length) d (t₂ + 1 + extra)).map observe =
        (evalConfigWithin (finishStoredGuess front.length back.length) d (t₂ + 1)).map observe := by
    rw [first] at hd
    have heq : d = prepared.resumeAt returnPc := by simpa using hd
    rw [heq, evalConfigWithin_add, PMF.map_bind]
    change (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepared.resumeAt returnPc) (t₂ + 1)).bind _ =
      (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepared.resumeAt returnPc) (t₂ + 1)).bind _
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext c hc
    rw [halted_eval _ _ (hCallerHalts c hc) extra, PMF.pure_map]
    rfl
  have hAfter := evalConfigWithin_after_return (finishStoredGuess front.length back.length) returnPc start
    t₁ (t₂ + 1) observe stable
  rw [first, PMF.pure_bind, hLastResult] at hAfter
  exact hAfter

theorem finishStoredGuess_haltsFrom (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) :
    ∀ c, PaddedRunsFor (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks) c
      (finishStoredGuessSteps front back bits) → c.halted = true := by
  intro c run
  have hc : (c.halted, c.outputBits) ∈ ((evalConfigWithin (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
      (finishStoredGuessSteps front back bits)).map (fun d => (d.halted, d.outputBits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [finishStoredGuess_evalResult] at hc
  have heq : (c.halted, c.outputBits) = (true, [taggedGuessValue bits == challenge]) := by simpa using hc
  exact congrArg Prod.fst heq

theorem finishStoredGuess_length (frontCount backCount : Nat) :
    (finishStoredGuess frontCount backCount).length = 8 * (frontCount + backCount) + 61 := by
  simp [finishStoredGuess, Program.withSubroutine, Program.asSubroutine_length,
    prepareStoredGuess_length, finishStoredTaggedGuess_length]
  omega

theorem finishStoredGuess_steps_le (front back : List (List Bool)) (bits : List Bool) :
    finishStoredGuessSteps front back bits ≤
      5 * bits.length + 4 * ((front.map List.length).sum + (back.map List.length).sum + front.length + back.length) + 33 := by
  have h := finishStoredTaggedGuess_steps_le back bits
  rw [finishStoredGuessSteps, prepareStoredGuessSteps, eraseOutputBlocks_steps]
  omega

/-- A common caller budget may exceed the branch's exact preparation and
parsing budget. Extra transitions stutter only after actual native halt. -/
theorem finishStoredGuess_evalResult_of_le (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks budget : Nat) (hFits : finishStoredGuessSteps front back bits ≤ budget) :
    (evalConfigWithin (finishStoredGuess front.length back.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
      budget).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
  rw [show budget = finishStoredGuessSteps front back bits + (budget - finishStoredGuessSteps front back bits) by omega,
    evalConfigWithin_add, PMF.map_bind]
  calc
    _ = (evalConfigWithin (finishStoredGuess front.length back.length)
        (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
        (finishStoredGuessSteps front back bits)).map (fun c => (c.halted, c.outputBits)) := by
      change (evalConfigWithin _ _ _).bind _ = (evalConfigWithin _ _ _).bind _
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext c hc
      have hHalted := finishStoredGuess_haltsFrom beforeInput boundary front back challenge bits inputBlanks outputBlanks c
        ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
      rw [halted_eval _ _ hHalted, PMF.pure_map]
      rfl
    _ = _ := finishStoredGuess_evalResult beforeInput boundary front back challenge bits inputBlanks outputBlanks

theorem finishStoredGuess_withSubroutine_evalOutput (pre suffix : Program) (returnPc : Nat)
    (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat)
    (hLayout : ∀ pc, pc ≤ (finishStoredGuess front.length back.length).length → pre.length + pc ≠ returnPc) :
    (evalReturnWithin (Program.withSubroutine pre (finishStoredGuess front.length back.length) suffix returnPc) returnPc
      ((prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks).rebasePc pre.length)
      (finishStoredGuessSteps front back bits)).map Configuration.outputBits =
      PMF.pure [taggedGuessValue bits == challenge] := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre (finishStoredGuess front.length back.length) suffix
    returnPc hLayout (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
    (by change 0 ≤ (finishStoredGuess front.length back.length).length; omega) rfl
    (finishStoredGuessSteps front back bits)
    (finishStoredGuess_haltsFrom beforeInput boundary front back challenge bits inputBlanks outputBlanks), PMF.map_comp]
  have h := congrArg (fun distribution : PMF (Bool × List Bool) => distribution.map Prod.snd)
    (finishStoredGuess_evalResult beforeInput boundary front back challenge bits inputBlanks outputBlanks)
  simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map,
    Configuration.resumeAt, Configuration.outputBits] using h

/-- Full native terminal processing on arbitrary finite physical tapes.
Paired rewind, front-block erasure, tagged comparison, back-block cleanup,
and final halt are all charged. Neither protocol validity nor a matching
parallel reply copy is required for this all-tape stopping certificate. -/
theorem finishStoredGuess_terminates_from_anyTape (frontCount backCount : Nat) (input output : Tape) :
    ∃ finish used,
      used ≤ 100000000 * (frontCount + 1) * (backCount + 1) * (output.cells + 1) ∧
      RunsFor (finishStoredGuess frontCount backCount)
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧ finish.halted = true := by
  obtain ⟨prepared, prepareTime, hPrepareTime, prepareRun, prepareHalt, _prepareLeft⟩ :=
    prepareStoredGuess_terminates_from_anyTape frontCount input output
  obtain ⟨cleaned, cleanTime, hCleanTime, cleanRun, cleanHalt⟩ :=
    finishStoredTaggedGuess_terminates_from_anyTape backCount prepared.inputTape prepared.outputTape
  let prepare := prepareStoredGuess frontCount
  let returnPc := prepare.length + 1
  let pre := prepare.asSubroutine 0 returnPc
  let cleanup := finishStoredTaggedGuess backCount
  let finalPc := pre.length + cleanup.length + 1
  obtain ⟨prepareUsed, hPrepareUsed, first⟩ := prepareRun.withSubroutine_halted
    [] prepare (cleanup.asSubroutine returnPc finalPc ++ [.halt]) returnPc (Nat.zero_le _) rfl prepareHalt
  have hPre : pre.length = returnPc := Program.asSubroutine_length _ _ _
  have firstProgram : Program.withSubroutine [] prepare
      (cleanup.asSubroutine returnPc finalPc ++ [.halt]) returnPc = finishStoredGuess frontCount backCount := by
    simp only [Program.withSubroutine, finishStoredGuess, List.length_nil, List.nil_append,
      pre, prepare, cleanup, finalPc, hPre, returnPc, List.append_assoc]
  rw [firstProgram] at first
  change RunsFor (finishStoredGuess frontCount backCount)
    ({ inputTape := input, outputTape := output } : Configuration) (prepared.resumeAt returnPc) prepareUsed at first
  obtain ⟨cleanUsed, hCleanUsed, second⟩ := cleanRun.withSubroutine_halted
    pre cleanup [.halt] finalPc (Nat.zero_le _) rfl cleanHalt
  have secondProgram : Program.withSubroutine pre cleanup [.halt] finalPc =
      finishStoredGuess frontCount backCount := rfl
  rw [secondProgram] at second
  have hEntry :
      ({ inputTape := prepared.inputTape, outputTape := prepared.outputTape } : Configuration).rebasePc pre.length =
      prepared.resumeAt returnPc := by simp [Configuration.rebasePc, Configuration.resumeAt, hPre]
  rw [hEntry] at second
  let finish : Configuration := { cleaned with pc := finalPc, halted := true }
  have last : Step (finishStoredGuess frontCount backCount) (cleaned.resumeAt finalPc) finish := by
    have code : (finishStoredGuess frontCount backCount)[finalPc]? = some .halt := by
      rw [← secondProgram]
      have h := Program.withSubroutine_getElem?_suffix pre cleanup [.halt] finalPc 0
      simpa only [Nat.add_zero, List.getElem?_cons_zero] using h
    simp [Step, successors, next, Configuration.resumeAt, finish, code, Instruction.next]
  refine ⟨finish, prepareUsed + cleanUsed + 1, ?_, RunsFor.succ (first.trans second) last, rfl⟩
  have hStorage := prepareRun.toPadded.outputTape_cells_le
  change prepared.outputTape.cells ≤ output.cells + prepareTime at hStorage
  have hCleanBound := hCleanTime.trans
    (Nat.mul_le_mul_left ((backCount + 1) * 10000) (Nat.add_le_add_right hStorage 1))
  have hScaledPrepare := Nat.mul_le_mul_left (backCount + 1) hPrepareTime
  ring_nf at hPrepareTime hCleanBound hScaledPrepare ⊢
  omega

theorem finishStoredGuess_no_randomBit (frontCount backCount : Nat) (tape : TapeId) :
    Instruction.randomBit tape ∉ finishStoredGuess frontCount backCount := by
  simp [finishStoredGuess, Program.withSubroutine, Program.asSubroutine, Instruction.asSubroutine]
  constructor
  · intro instruction hMem hEq
    cases instruction <;> simp_all [prepareStoredGuess_no_randomBit]
  · intro instruction hMem hEq
    cases instruction <;> simp_all [finishStoredTaggedGuess_no_randomBit]

theorem finishStoredGuess_haltsFrom_anyTape (frontCount backCount : Nat) (input output : Tape)
    (finish : Configuration)
    (run : PaddedRunsFor (finishStoredGuess frontCount backCount)
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (100000000 * (frontCount + 1) * (backCount + 1) * (output.cells + 1))) : finish.halted = true := by
  obtain ⟨target, used, hBound, actual, hHalt⟩ :=
    finishStoredGuess_terminates_from_anyTape frontCount backCount input output
  exact actual.haltsFrom_of_no_randomBit hHalt (finishStoredGuess_no_randomBit frontCount backCount)
    hBound finish run

end Machine
