import Foundation.Crypto.Semantics.Machine.TaggedGuess
import Foundation.Crypto.Semantics.Machine.GuardedResult

namespace Machine

/-- Rewind two copies of a source output in lockstep. Preserve the input
copy, explicitly erase the output copy, and leave the saved challenge bit
immediately left of a fresh output cell. The input's blank separator stops
the scan before caller-owned data; every branch, move, and erase is charged. -/
def prepareCopiedGuess : Program :=
  [.moveLeft .input, .moveLeft .output, .branch .input 5 3 3,
   .erase .output, .jump 0, .moveRight .input, .moveRight .output, .halt]

private def copiedGuessState (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (blanks : Nat) : Configuration :=
  { inputTape := {
      left := left.map some ++ none :: beforeInput
      current := current
      right := right },
    outputTape := {
      left := left.map some ++ some challenge :: beforeOutput
      right := List.replicate blanks none } }

private def copiedGuessFinish (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (blanks : Nat) : Configuration :=
  { pc := 7,
    inputTape := ({
      left := beforeInput
      right := left.reverse.map some ++ current :: right } : Tape).moveRight,
    outputTape := {
      left := some challenge :: beforeOutput
      right := List.replicate (blanks + left.length) none },
    halted := true }

private theorem copiedGuess_run (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (blanks : Nat) :
    RunsFor prepareCopiedGuess
      (copiedGuessState beforeInput beforeOutput challenge left current right blanks)
      (copiedGuessFinish beforeInput beforeOutput challenge left current right blanks)
      (5 * left.length + 6) := by
  induction left generalizing current right blanks with
  | nil =>
      let start := copiedGuessState beforeInput beforeOutput challenge [] current right blanks
      let movedInput : Configuration := { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let movedOutput : Configuration := { movedInput with pc := 2, outputTape := movedInput.outputTape.moveLeft }
      let selected : Configuration := { movedOutput with pc := 5 }
      let restoredInput : Configuration := { selected with pc := 6, inputTape := selected.inputTape.moveRight }
      let restoredOutput : Configuration := { restoredInput with pc := 7, outputTape := restoredInput.outputTape.moveRight }
      have h1 : Step prepareCopiedGuess start movedInput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput,
          copiedGuessState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step prepareCopiedGuess movedInput movedOutput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          copiedGuessState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h3 : Step prepareCopiedGuess movedOutput selected := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, copiedGuessState, Instruction.next, Configuration.tape, Tape.moveLeft]
      have h4 : Step prepareCopiedGuess selected restoredInput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, restoredInput, copiedGuessState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have h5 : Step prepareCopiedGuess restoredInput restoredOutput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, restoredInput, restoredOutput, copiedGuessState, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have h6 : Step prepareCopiedGuess restoredOutput
          (copiedGuessFinish beforeInput beforeOutput challenge [] current right blanks) := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, restoredInput, restoredOutput, copiedGuessState, copiedGuessFinish,
          Instruction.next, Tape.moveLeft, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5) h6
  | cons bit rest ih =>
      let start := copiedGuessState beforeInput beforeOutput challenge (bit :: rest) current right blanks
      let movedInput : Configuration := { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let movedOutput : Configuration := { movedInput with pc := 2, outputTape := movedInput.outputTape.moveLeft }
      let selected : Configuration := { movedOutput with pc := 3 }
      let erased : Configuration := { selected with pc := 4, outputTape := selected.outputTape.write none }
      have h1 : Step prepareCopiedGuess start movedInput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput,
          copiedGuessState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step prepareCopiedGuess movedInput movedOutput := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          copiedGuessState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h3 : Step prepareCopiedGuess movedOutput selected := by
        cases bit <;> simp [Step, successors, next, prepareCopiedGuess, start, movedInput,
          movedOutput, selected, copiedGuessState, Instruction.next, Configuration.tape,
          Tape.moveLeft]
      have h4 : Step prepareCopiedGuess selected erased := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, erased, copiedGuessState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have h5 : Step prepareCopiedGuess erased
          (copiedGuessState beforeInput beforeOutput challenge rest (some bit)
            (current :: right) (blanks + 1)) := by
        simp [Step, successors, next, prepareCopiedGuess, start, movedInput, movedOutput,
          selected, erased, copiedGuessState, Instruction.next, Tape.moveLeft, Tape.write,
          List.replicate_succ]
      have hFinish : copiedGuessFinish beforeInput beforeOutput challenge rest (some bit)
          (current :: right) (blanks + 1) =
          copiedGuessFinish beforeInput beforeOutput challenge (bit :: rest) current right blanks := by
        simp [copiedGuessFinish, List.reverse_cons, List.map_append, List.append_assoc,
          Nat.add_comm, Nat.add_left_comm]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h1) h2) h3) h4) h5).trans
          (ih (some bit) (current :: right) (blanks + 1))
      rw [hFinish] at run
      convert run using 1
      simp [List.length_cons]
      omega

/-- The physical form produced by guarded raw-output extraction. The input
separator and saved challenge are part of the actual starting tapes. -/
def prepareCopiedGuessStart (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) : Configuration :=
  copiedGuessState beforeInput beforeOutput challenge bits.reverse none [] blanks

def prepareCopiedGuessFinish (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 7,
    inputTape := ({ left := beforeInput, right := bits.map some ++ [none] } : Tape).moveRight,
    outputTape := {
      left := some challenge :: beforeOutput
      right := List.replicate (blanks + bits.length) none },
    halted := true }

theorem prepareCopiedGuess_runs (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    RunsFor prepareCopiedGuess (prepareCopiedGuessStart beforeInput beforeOutput challenge bits blanks)
      (prepareCopiedGuessFinish beforeInput beforeOutput challenge bits blanks)
      (5 * bits.length + 6) := by
  simpa [prepareCopiedGuessStart, prepareCopiedGuessFinish, copiedGuessFinish] using
    copiedGuess_run beforeInput beforeOutput challenge bits.reverse none [] blanks

theorem prepareCopiedGuess_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareCopiedGuess := by simp [prepareCopiedGuess]

theorem prepareCopiedGuess_eval (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    evalConfigWithin prepareCopiedGuess (prepareCopiedGuessStart beforeInput beforeOutput challenge bits blanks)
      (5 * bits.length + 6) =
      PMF.pure (prepareCopiedGuessFinish beforeInput beforeOutput challenge bits blanks) :=
  (prepareCopiedGuess_runs beforeInput beforeOutput challenge bits blanks).evalConfigWithin_eq_pure_of_no_randomBit
    prepareCopiedGuess_no_randomBit

theorem prepareCopiedGuess_control_closed (c d : Configuration)
    (hPc : c.pc < prepareCopiedGuess.length) (step : Step prepareCopiedGuess c d)
    (_hRunning : d.halted = false) : d.pc < prepareCopiedGuess.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 8 at hPc
  change d.pc < 8
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareCopiedGuess,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem getD_append_final_blank (bits : List Bool) (i : Nat) :
    (bits.map some ++ [none]).getD i none = (bits.map some).getD i none := by
  induction bits generalizing i with
  | nil => cases i <;> simp
  | cons bit rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.map_cons, List.cons_append, List.getD_cons_succ] using ih i

/-- Extra blank cells left by real erasure and head movement have the same
cell semantics as the parser's specified starting state. This is an equality
of observations, not a tape cleanup performed at zero transition cost. -/
theorem prepareCopiedGuessFinish_equivalent (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    ((prepareCopiedGuessFinish beforeInput beforeOutput challenge bits blanks).resumeAt 0).Equivalent
      (finishTaggedGuessStart (none :: beforeInput) beforeOutput challenge bits) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases bits with
    | nil => exact Tape.Equivalent.refl _
    | cons bit rest =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        simpa [prepareCopiedGuessFinish, finishTaggedGuessStart, readTaggedGuessStart,
          Tape.moveRight, Tape.ofBits, Configuration.resumeAt] using getD_append_final_blank rest i
  · refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    simp [prepareCopiedGuessFinish, finishTaggedGuessStart, readTaggedGuessStart, Configuration.resumeAt, List.getElem?_replicate]
    split <;> rfl

/-- Exact compatibility with the physical output of a guarded source call.
The stored challenge is retained; source-output erasure is still performed
by the eight native instructions of `prepareCopiedGuess`. -/
theorem rawResultFrom_prepareCopiedGuessStart (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (challenge : Bool) (c : Configuration) :
    (GuardedCompiler.rawResultFrom source input beforeInput (some challenge :: beforeOutput) c).resumeAt 0 =
      prepareCopiedGuessStart
        ((GuardedCompiler.encodedRightBits c.inputTape).reverse.map some ++
          (GuardedCompiler.encodeTape (input.reverse.map some ++ beforeInput) c.inputTape).left)
        beforeOutput challenge c.outputBits (2 * c.outputTape.cells + 2 - c.outputBits.length) := by
  simp only [GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
    GuardedCompiler.copyScratchFinish, GuardedCompiler.scratchPrefix, Configuration.resumeAt,
    prepareCopiedGuessStart, copiedGuessState, List.map_reverse]
  rfl

theorem prepareCopiedGuess_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (challenge : Bool)
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin (Program.withSubroutine pre prepareCopiedGuess suffix returnPc)
      ((prepareCopiedGuessStart beforeInput beforeOutput challenge bits blanks).rebasePc pre.length)
      (5 * bits.length + 6) =
      PMF.pure ((prepareCopiedGuessFinish beforeInput beforeOutput challenge bits blanks).resumeAt returnPc) :=
  (prepareCopiedGuess_runs beforeInput beforeOutput challenge bits blanks).evalConfigWithin_withSubroutine_halted_of_closed
    pre prepareCopiedGuess suffix returnPc
    (by simp [prepareCopiedGuessStart, copiedGuessState, prepareCopiedGuess])
    rfl rfl prepareCopiedGuess_control_closed prepareCopiedGuess_no_randomBit

/-- Complete native guess-output continuation, starting from the two copies
left by guarded extraction. Erase the output copy, rewind the input copy,
interpret the tagged guess, compare with the saved challenge, and halt. -/
def finishCopiedGuess : Program :=
  prepareCopiedGuess.asSubroutine 0 9 ++ finishTaggedGuess.asSubroutine 9 37 ++ [.halt]

def finishCopiedGuessSteps (bits : List Bool) : Nat :=
  (5 * bits.length + 6) + (readTaggedGuessBudget bits + 7 + 1)

theorem finishCopiedGuess_steps_le (bits : List Bool) :
    finishCopiedGuessSteps bits ≤ 5 * bits.length + 21 := by
  have h := readTaggedGuess_budget_le bits
  dsimp [finishCopiedGuessSteps]
  omega

/-- Full native probability semantics of the final continuation. Physical
blank padding is retained; tape equivalence is used only to prove identical
observations after the same actual machine transitions. -/
theorem finishCopiedGuess_evalResult (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks)
      (finishCopiedGuessSteps bits)).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
  have prep := prepareCopiedGuess_withSubroutine_eval []
    (finishTaggedGuess.asSubroutine 9 37 ++ [.halt]) 9 beforeInput [] challenge bits blanks
  change evalConfigWithin finishCopiedGuess
    (prepareCopiedGuessStart beforeInput [] challenge bits blanks) (5 * bits.length + 6) =
    PMF.pure ((prepareCopiedGuessFinish beforeInput [] challenge bits blanks).resumeAt 9) at prep
  let start := (prepareCopiedGuessFinish beforeInput [] challenge bits blanks).resumeAt 0
  have hEquivalent : start.Equivalent
      (finishTaggedGuessStart (none :: beforeInput) [] challenge bits) :=
    prepareCopiedGuessFinish_equivalent beforeInput [] challenge bits blanks
  have hHaltEval : (evalConfigWithin finishTaggedGuess start
      (readTaggedGuessBudget bits + 7)).map Configuration.halted = PMF.pure true := by
    rw [evalConfigWithin_map_eq_of_equivalent finishTaggedGuess start _ hEquivalent _
      Configuration.halted (fun _ _ h => h.2.1), finishTaggedGuess_eval]
    simp only [PMF.map, PMF.pure_bind, Function.comp_apply, finishTaggedGuessFinish]
  have halts : ∀ c, PaddedRunsFor finishTaggedGuess start c
      (readTaggedGuessBudget bits + 7) → c.halted = true := by
    intro c run
    have hMem : c.halted ∈ ((evalConfigWithin finishTaggedGuess start
        (readTaggedGuessBudget bits + 7)).map Configuration.halted).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
    rw [hHaltEval] at hMem
    simpa using hMem
  have finalCall := Program.evalConfigWithin_withSubroutine_final_halt
    (prepareCopiedGuess.asSubroutine 0 9) finishTaggedGuess start
    (by simp [start, Configuration.resumeAt, finishTaggedGuess, Program.asSubroutine_length,
      readTaggedGuess, matchPreviousOutputBit]) rfl (readTaggedGuessBudget bits + 7) halts
  have hProgram : Program.withSubroutine (prepareCopiedGuess.asSubroutine 0 9) finishTaggedGuess
      [.halt] ((prepareCopiedGuess.asSubroutine 0 9).length + finishTaggedGuess.length + 1) =
      finishCopiedGuess := by
    simp [Program.withSubroutine, Program.asSubroutine_length, finishCopiedGuess,
      prepareCopiedGuess, finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit]
  dsimp only at finalCall
  rw [hProgram] at finalCall
  have hEntry : start.rebasePc (prepareCopiedGuess.asSubroutine 0 9).length =
      (prepareCopiedGuessFinish beforeInput [] challenge bits blanks).resumeAt 9 := rfl
  rw [hEntry] at finalCall
  rw [finishCopiedGuessSteps, evalConfigWithin_add, prep, PMF.pure_bind, finalCall, PMF.map_comp]
  change (evalConfigWithin finishTaggedGuess start (readTaggedGuessBudget bits + 7)).map
    (fun c => (true, c.outputBits)) = _
  rw [evalConfigWithin_map_eq_of_equivalent finishTaggedGuess start _ hEquivalent _
    (fun c => (true, c.outputBits)) (fun _ _ h => congrArg (fun bits => (true, bits)) h.outputBits),
    finishTaggedGuess_eval]
  simp only [PMF.map, PMF.pure_bind, Function.comp_apply, finishTaggedGuessFinish_outputBits]

theorem finishCopiedGuess_evalOutput (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks)
      (finishCopiedGuessSteps bits)).map Configuration.outputBits =
      PMF.pure [taggedGuessValue bits == challenge] := by
  have h := congrArg (fun distribution : PMF (Bool × List Bool) => distribution.map Prod.snd)
    (finishCopiedGuess_evalResult beforeInput challenge bits blanks)
  simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map] using h

theorem finishCopiedGuess_haltsFrom (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    ∀ c, PaddedRunsFor finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks) c (finishCopiedGuessSteps bits) →
      c.halted = true := by
  intro c run
  have hMem : (c.halted, c.outputBits) ∈ ((evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks) (finishCopiedGuessSteps bits)).map
        (fun c => (c.halted, c.outputBits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [finishCopiedGuess_evalResult] at hMem
  have hEq : (c.halted, c.outputBits) = (true, [taggedGuessValue bits == challenge]) := by
    simpa using hMem
  exact congrArg Prod.fst hEq

/-- Apply the continuation to exactly the physical configuration produced
by a guarded source call. Changing to relative PC zero is notation for the
callee's local entry; embedding supplies the actual caller address. -/
theorem finishCopiedGuess_rawResult_eval (source : Program) (input : List Bool)
    (beforeInput : List (Option Bool)) (challenge : Bool) (c : Configuration) :
    (evalConfigWithin finishCopiedGuess
      ((GuardedCompiler.rawResultFrom source input beforeInput [some challenge] c).resumeAt 0)
      (finishCopiedGuessSteps c.outputBits)).map (fun d => (d.halted, d.outputBits)) =
      PMF.pure (true, [taggedGuessValue c.outputBits == challenge]) := by
  rw [rawResultFrom_prepareCopiedGuessStart]
  exact finishCopiedGuess_evalResult _ _ _ _

/-- The entire cleanup and comparison can be called from arbitrary finite
wrapper code, including code which uses random-bit instructions. -/
theorem finishCopiedGuess_withSubroutine_evalOutput
    (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ finishCopiedGuess.length → pre.length + pc ≠ returnPc)
    (beforeInput : List (Option Bool)) (challenge : Bool) (bits : List Bool) (blanks : Nat) :
    (evalReturnWithin (Program.withSubroutine pre finishCopiedGuess suffix returnPc) returnPc
      ((prepareCopiedGuessStart beforeInput [] challenge bits blanks).rebasePc pre.length)
      (finishCopiedGuessSteps bits)).map Configuration.outputBits =
      PMF.pure [taggedGuessValue bits == challenge] := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre finishCopiedGuess suffix
    returnPc hLayout (prepareCopiedGuessStart beforeInput [] challenge bits blanks)
    (by simp [prepareCopiedGuessStart, copiedGuessState]) rfl (finishCopiedGuessSteps bits)
    (finishCopiedGuess_haltsFrom beforeInput challenge bits blanks), PMF.map_comp]
  change (evalConfigWithin finishCopiedGuess
    (prepareCopiedGuessStart beforeInput [] challenge bits blanks)
    (finishCopiedGuessSteps bits)).map Configuration.outputBits = _
  exact finishCopiedGuess_evalOutput beforeInput challenge bits blanks

private theorem eval_halted (p : Program) (c : Configuration) (hc : c.halted = true)
    (extra : Nat) : evalConfigWithin p c extra = PMF.pure c := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, hc]

/-- The same halted result distribution at every larger budget. Extra fuel
stutters only after the actual native stopping transitions have occurred. -/
theorem finishCopiedGuess_evalResult_of_le (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks budget : Nat)
    (hFits : finishCopiedGuessSteps bits ≤ budget) :
    (evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks) budget).map
        (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
  rw [show budget = finishCopiedGuessSteps bits + (budget - finishCopiedGuessSteps bits) by omega,
    evalConfigWithin_add, PMF.map_bind]
  calc
    _ = (evalConfigWithin finishCopiedGuess
        (prepareCopiedGuessStart beforeInput [] challenge bits blanks)
        (finishCopiedGuessSteps bits)).map (fun c => (c.halted, c.outputBits)) := by
      change (evalConfigWithin _ _ _).bind _ = (evalConfigWithin _ _ _).bind _
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext c hc
      have hHalted := finishCopiedGuess_haltsFrom beforeInput challenge bits blanks c
        ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
      rw [eval_halted _ _ hHalted, PMF.pure_map]
      rfl
    _ = _ := finishCopiedGuess_evalResult beforeInput challenge bits blanks

theorem finishCopiedGuess_haltsFrom_of_le (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) (blanks budget : Nat)
    (hFits : finishCopiedGuessSteps bits ≤ budget) :
    ∀ c, PaddedRunsFor finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks) c budget → c.halted = true := by
  intro c run
  have hMem : (c.halted, c.outputBits) ∈ ((evalConfigWithin finishCopiedGuess
      (prepareCopiedGuessStart beforeInput [] challenge bits blanks) budget).map
        (fun c => (c.halted, c.outputBits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [finishCopiedGuess_evalResult_of_le _ _ _ _ _ hFits] at hMem
  have hEq : (c.halted, c.outputBits) = (true, [taggedGuessValue bits == challenge]) := by
    simpa using hMem
  exact congrArg Prod.fst hEq

end Machine
