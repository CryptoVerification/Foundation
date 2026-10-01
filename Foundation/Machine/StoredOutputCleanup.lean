import Foundation.Machine.BitstringErasure

namespace Machine

/-- Save the current output bit in the current input cell and erase its
old output cell. This is used only after guess parsing, when overwriting
that input cell is permitted. The bit is copied by native branches/writes. -/
def saveCurrentOutputBit : Program :=
  [.branch .output 6 1 3, .write .input false, .jump 5,
   .write .input true, .jump 5, .erase .output, .halt]

def saveCurrentOutputBitStart (input : Tape) (left right : List (Option Bool))
    (bit : Bool) : Configuration :=
  { inputTape := input, outputTape := { left := left, current := some bit, right := right } }

def saveCurrentOutputBitFinish (input : Tape) (left right : List (Option Bool))
    (bit : Bool) : Configuration :=
  { pc := 6, inputTape := input.write (some bit),
    outputTape := { left := left, right := right }, halted := true }

theorem saveCurrentOutputBit_eval_before_halt (input : Tape) (left right : List (Option Bool))
    (bit : Bool) :
    evalConfigWithin saveCurrentOutputBit (saveCurrentOutputBitStart input left right bit) 4 =
      PMF.pure { saveCurrentOutputBitFinish input left right bit with halted := false } := by
  cases bit <;> simp [evalConfigWithin, saveCurrentOutputBit, saveCurrentOutputBitStart,
    saveCurrentOutputBitFinish, stepPMF, next, Instruction.next, Configuration.tape,
    Configuration.updateTape, Configuration.advance, Tape.write]

theorem saveCurrentOutputBit_runs (input : Tape) (left right : List (Option Bool)) (bit : Bool) :
    RunsFor saveCurrentOutputBit (saveCurrentOutputBitStart input left right bit)
      (saveCurrentOutputBitFinish input left right bit) 5 := by
  have prior : PaddedRunsFor saveCurrentOutputBit (saveCurrentOutputBitStart input left right bit)
      { saveCurrentOutputBitFinish input left right bit with halted := false } 4 := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [saveCurrentOutputBit_eval_before_halt]; simp
  have last : Step saveCurrentOutputBit
      { saveCurrentOutputBitFinish input left right bit with halted := false }
      (saveCurrentOutputBitFinish input left right bit) := by
    simp [Step, successors, next, saveCurrentOutputBit, saveCurrentOutputBitFinish, Instruction.next]
  exact RunsFor.succ (prior.toRunsFor_of_running rfl) last

theorem saveCurrentOutputBit_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ saveCurrentOutputBit := by simp [saveCurrentOutputBit]

theorem saveCurrentOutputBit_control_closed (c d : Configuration)
    (hPc : c.pc < saveCurrentOutputBit.length) (step : Step saveCurrentOutputBit c d)
    (_hRunning : d.halted = false) : d.pc < saveCurrentOutputBit.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 7 at hPc
  change d.pc < 7
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, saveCurrentOutputBit,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Emit the already saved input bit into the current output cell. -/
def writeSavedInputBit : Program :=
  [.branch .input 1 1 3, .write .output false, .halt, .write .output true, .halt]

def writeSavedInputBitStart (input : Tape) (output : Tape) (bit : Bool) : Configuration :=
  { inputTape := input.write (some bit), outputTape := output }

def writeSavedInputBitFinish (input : Tape) (output : Tape) (bit : Bool) : Configuration :=
  { pc := if bit then 4 else 2,
    inputTape := input.write (some bit), outputTape := output.write (some bit), halted := true }

theorem writeSavedInputBit_eval (input : Tape) (output : Tape) (bit : Bool) :
    evalConfigWithin writeSavedInputBit (writeSavedInputBitStart input output bit) 3 =
      PMF.pure (writeSavedInputBitFinish input output bit) := by
  cases bit <;> simp [evalConfigWithin, writeSavedInputBit, writeSavedInputBitStart,
    writeSavedInputBitFinish, stepPMF, next, Instruction.next, Configuration.tape,
    Configuration.updateTape, Configuration.advance, Tape.write]

theorem writeSavedInputBit_haltsFrom (input : Tape) (output : Tape) (bit : Bool) :
    ∀ c, PaddedRunsFor writeSavedInputBit (writeSavedInputBitStart input output bit) c 3 → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [writeSavedInputBit_eval] at hc
  have heq : c = writeSavedInputBitFinish input output bit := by simpa using hc
  rw [heq]; rfl

/-- Preserve a decoded comparison bit, erase a fixed number of retained
scratch blocks, and emit that bit on the physically cleared output tape.
The program depends only on the number of protocol blocks. Their contents,
lengths, input data and comparison bit are not embedded into the code. -/
def cleanStoredOutputBit (count : Nat) : Program :=
  let pre := saveCurrentOutputBit.asSubroutine 0 8
  let eraser := eraseOutputBlocks count
  let emitPc := 8 + eraser.length + 1
  pre ++ eraser.asSubroutine 8 emitPc ++ writeSavedInputBit.asSubroutine emitPc (emitPc + 6) ++ [.halt]

def cleanStoredOutputBitStart (input : Tape) (blocks : List (List Bool))
    (right : List (Option Bool)) (bit : Bool) : Configuration :=
  saveCurrentOutputBitStart input (savedOutputBlocks blocks) right bit

def cleanStoredOutputBitFinish (input : Tape) (blocks : List (List Bool))
    (right : List (Option Bool)) (bit : Bool) : Configuration :=
  { pc := 8 + (eraseOutputBlocks blocks.length).length + 1 + 6,
    inputTape := input.write (some bit),
    outputTape := {
      current := some bit
      right := List.replicate ((blocks.map List.length).sum + blocks.length) none ++ right },
    halted := true }

def cleanStoredOutputBitSteps (blocks : List (List Bool)) : Nat :=
  5 + eraseOutputBlocksSteps blocks + 4

private theorem halted_eval (p : Program) (c : Configuration) (h : c.halted = true) (extra : Nat) :
    evalConfigWithin p c extra = PMF.pure c := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, h]

theorem cleanStoredOutputBit_eval (input : Tape) (blocks : List (List Bool))
    (right : List (Option Bool)) (bit : Bool) :
    evalConfigWithin (cleanStoredOutputBit blocks.length)
      (cleanStoredOutputBitStart input blocks right bit) (cleanStoredOutputBitSteps blocks) =
      PMF.pure (cleanStoredOutputBitFinish input blocks right bit) := by
  let pre := saveCurrentOutputBit.asSubroutine 0 8
  let eraser := eraseOutputBlocks blocks.length
  let emitPc := 8 + eraser.length + 1
  let suffix := writeSavedInputBit.asSubroutine emitPc (emitPc + 6) ++ [.halt]
  let saved := input.write (some bit)
  let eraseStart := eraseOutputBlocksStart saved [] blocks right
  let erased := eraseOutputBlocksFinish saved [] blocks right
  let clean : Tape := { right := List.replicate ((blocks.map List.length).sum + blocks.length) none ++ right }
  let emitStart := writeSavedInputBitStart input clean bit
  have hPre : pre.length = 8 := rfl
  have hProgram : Program.withSubroutine pre eraser suffix emitPc = cleanStoredOutputBit blocks.length := by
    simp only [Program.withSubroutine, hPre, cleanStoredOutputBit, pre, eraser, emitPc, suffix,
      List.append_assoc]
  have first := (saveCurrentOutputBit_runs input (savedOutputBlocks blocks) right bit).evalConfigWithin_withSubroutine_halted_of_closed
    [] saveCurrentOutputBit (eraser.asSubroutine 8 emitPc ++ suffix) 8
    (by change 0 < 7; decide) rfl rfl saveCurrentOutputBit_control_closed saveCurrentOutputBit_no_randomBit
  have hFirstProgram : Program.withSubroutine [] saveCurrentOutputBit
      (eraser.asSubroutine 8 emitPc ++ suffix) 8 = cleanStoredOutputBit blocks.length := by
    simp only [Program.withSubroutine, List.length_nil, List.nil_append,
      cleanStoredOutputBit, eraser, emitPc, suffix, List.append_assoc]
  rw [hFirstProgram] at first
  simp only [List.length_nil] at first
  have hFirstStart : (saveCurrentOutputBitStart input (savedOutputBlocks blocks) right bit).rebasePc 0 =
      cleanStoredOutputBitStart input blocks right bit := by
    simp [Configuration.rebasePc, saveCurrentOutputBitStart, cleanStoredOutputBitStart]
  have hFirstFinish : (saveCurrentOutputBitFinish input (savedOutputBlocks blocks) right bit).resumeAt 8 =
      eraseStart.rebasePc pre.length := by
    simp [saveCurrentOutputBitFinish, Configuration.resumeAt, Configuration.rebasePc,
      eraseStart, eraseOutputBlocksStart, saved, hPre]
  rw [hFirstStart, hFirstFinish] at first
  have hErased := eraseOutputBlocks_withSubroutine_eval pre suffix emitPc saved [] blocks right
    (by intro pc hpc; rw [hPre]; dsimp only [emitPc, eraser]; omega)
  rw [hProgram] at hErased
  change evalReturnWithin (cleanStoredOutputBit blocks.length) emitPc (eraseStart.rebasePc pre.length)
    (eraseOutputBlocksSteps blocks) = PMF.pure (erased.resumeAt emitPc) at hErased
  let emitPre := pre ++ eraser.asSubroutine 8 emitPc
  have hEmitPre : emitPre.length = emitPc := by
    simp only [emitPre, List.length_append, hPre, Program.asSubroutine_length, emitPc, Nat.add_assoc]
  have last := Program.evalConfigWithin_withSubroutine_final_halt emitPre writeSavedInputBit emitStart
    (by change 0 ≤ 5; omega) rfl 3 (writeSavedInputBit_haltsFrom input clean bit)
  have hLastProgram : Program.withSubroutine emitPre writeSavedInputBit [.halt]
      (emitPre.length + writeSavedInputBit.length + 1) = cleanStoredOutputBit blocks.length := by
    simp only [Program.withSubroutine, emitPre, hEmitPre, cleanStoredOutputBit,
      pre, eraser, emitPc, show writeSavedInputBit.length = 5 from rfl, List.append_assoc]
  dsimp only at last
  rw [hLastProgram, writeSavedInputBit_eval] at last
  have hEntry : emitStart.rebasePc emitPre.length = erased.resumeAt emitPc := by
    simp [emitStart, writeSavedInputBitStart, clean, erased, eraseOutputBlocksFinish,
      saved, Tape.write, Configuration.resumeAt, Configuration.rebasePc, hEmitPre]
  rw [hEntry] at last
  have hLast : evalConfigWithin (cleanStoredOutputBit blocks.length) (erased.resumeAt emitPc) 4 =
      PMF.pure (cleanStoredOutputBitFinish input blocks right bit) := by
    simpa [PMF.pure_map, hEmitPre, writeSavedInputBitFinish, cleanStoredOutputBitFinish,
      clean, emitPc, eraser, Tape.write, show writeSavedInputBit.length = 5 from rfl,
      Nat.add_assoc] using last
  have hTail (d : Configuration) (hd : d ∈ (evalReturnWithin (cleanStoredOutputBit blocks.length)
      emitPc (eraseStart.rebasePc pre.length) (eraseOutputBlocksSteps blocks)).support)
      (_hPc : d.pc = emitPc) (extra : Nat) :
      (evalConfigWithin (cleanStoredOutputBit blocks.length) d (4 + extra)).map id =
        (evalConfigWithin (cleanStoredOutputBit blocks.length) d 4).map id := by
    rw [hErased] at hd
    have heq : d = erased.resumeAt emitPc := by simpa using hd
    rw [heq, evalConfigWithin_add, hLast, PMF.pure_bind,
      halted_eval _ _ rfl extra]
  have hAfter := evalConfigWithin_after_return (cleanStoredOutputBit blocks.length) emitPc
    (eraseStart.rebasePc pre.length) (eraseOutputBlocksSteps blocks) 4 id hTail
  simp only [PMF.map_id] at hAfter
  rw [hErased, PMF.pure_bind, hLast] at hAfter
  rw [cleanStoredOutputBitSteps, Nat.add_assoc, evalConfigWithin_add, first, PMF.pure_bind, hAfter]

theorem cleanStoredOutputBit_length (count : Nat) : (cleanStoredOutputBit count).length = 8 * count + 17 := by
  simp [cleanStoredOutputBit, eraseOutputBlocks_length, saveCurrentOutputBit, writeSavedInputBit,
    Program.asSubroutine_length]
  omega

theorem cleanStoredOutputBit_steps (blocks : List (List Bool)) :
    cleanStoredOutputBitSteps blocks = 4 * ((blocks.map List.length).sum + blocks.length) + 10 := by
  rw [cleanStoredOutputBitSteps, eraseOutputBlocks_steps]; omega

theorem cleanStoredOutputBitFinish_output (input : Tape) (blocks : List (List Bool))
    (blanks : Nat) (bit : Bool) :
    (cleanStoredOutputBitFinish input blocks (List.replicate blanks none) bit).outputBits = [bit] := by
  simp [cleanStoredOutputBitFinish, Configuration.outputBits, Tape.bits, List.filterMap_append]

theorem cleanStoredOutputBit_haltsFrom (input : Tape) (blocks : List (List Bool))
    (right : List (Option Bool)) (bit : Bool) :
    ∀ c, PaddedRunsFor (cleanStoredOutputBit blocks.length)
      (cleanStoredOutputBitStart input blocks right bit) c (cleanStoredOutputBitSteps blocks) → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [cleanStoredOutputBit_eval] at hc
  have heq : c = cleanStoredOutputBitFinish input blocks right bit := by simpa using hc
  rw [heq]; rfl

end Machine
