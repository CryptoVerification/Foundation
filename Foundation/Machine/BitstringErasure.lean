import Foundation.Machine.SubroutineProbability

namespace Machine

/-- Erase one contiguous output block, scanning left from its following
blank to its preceding blank. Saved cells beyond the preceding blank and
the entire input tape are preserved. Each inspected bit costs four native
transitions; this is not a whole-tape reset instruction. -/
def eraseOutputBlock : Program :=
  [.moveLeft .output, .branch .output 4 2 2,
   .erase .output, .jump 0, .halt]

private def eraseBlockState (input : Tape) (before : List (Option Bool))
    (left : List Bool) (right : List (Option Bool)) : Configuration :=
  { inputTape := input,
    outputTape := { left := left.map some ++ none :: before, right := right } }

private def eraseBlockFinish (input : Tape) (before : List (Option Bool))
    (left : List Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 4, inputTape := input,
    outputTape := {
      left := before
      right := List.replicate (left.length + 1) none ++ right },
    halted := true }

private theorem eraseBlock_run (input : Tape) (before : List (Option Bool))
    (left : List Bool) (right : List (Option Bool)) :
    RunsFor eraseOutputBlock (eraseBlockState input before left right)
      (eraseBlockFinish input before left right) (4 * left.length + 3) := by
  induction left generalizing right with
  | nil =>
      let moved : Configuration :=
        { eraseBlockState input before [] right with
          pc := 1
          outputTape := (eraseBlockState input before [] right).outputTape.moveLeft }
      let selected : Configuration := { moved with pc := 4 }
      have h₁ : Step eraseOutputBlock (eraseBlockState input before [] right) moved := by
        simp [Step, successors, next, eraseOutputBlock, moved, eraseBlockState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₂ : Step eraseOutputBlock moved selected := by
        simp [Step, successors, next, eraseOutputBlock, moved, selected, eraseBlockState,
          Instruction.next, Configuration.tape, Tape.moveLeft]
      have h₃ : Step eraseOutputBlock selected (eraseBlockFinish input before [] right) := by
        simp [Step, successors, next, eraseOutputBlock, moved, selected, eraseBlockState,
          eraseBlockFinish, Instruction.next, Tape.moveLeft]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h₁) h₂) h₃
  | cons bit rest ih =>
      let start := eraseBlockState input before (bit :: rest) right
      let moved : Configuration := { start with pc := 1, outputTape := start.outputTape.moveLeft }
      let selected : Configuration := { moved with pc := 2 }
      let erased : Configuration := { selected with pc := 3, outputTape := selected.outputTape.write none }
      have h₁ : Step eraseOutputBlock start moved := by
        simp [Step, successors, next, eraseOutputBlock, start, moved, eraseBlockState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₂ : Step eraseOutputBlock moved selected := by
        cases bit <;> simp [Step, successors, next, eraseOutputBlock, start, moved,
          selected, eraseBlockState, Instruction.next, Configuration.tape, Tape.moveLeft]
      have h₃ : Step eraseOutputBlock selected erased := by
        simp [Step, successors, next, eraseOutputBlock, start, moved, selected, erased, eraseBlockState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₄ : Step eraseOutputBlock erased (eraseBlockState input before rest (none :: right)) := by
        simp [Step, successors, next, eraseOutputBlock, start, moved, selected, erased,
          eraseBlockState, Instruction.next, Tape.moveLeft, Tape.write]
      have hFinish : eraseBlockFinish input before rest (none :: right) =
          eraseBlockFinish input before (bit :: rest) right := by
        simp only [eraseBlockFinish, List.length_cons]
        simp only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h₁) h₂) h₃) h₄).trans (ih (none :: right))
      rw [hFinish] at run
      convert run using 1
      simp [List.length_cons]
      omega

def eraseOutputBlockStart (input : Tape) (before : List (Option Bool))
    (bits : List Bool) (right : List (Option Bool)) : Configuration :=
  eraseBlockState input before bits.reverse right

def eraseOutputBlockFinish (input : Tape) (before : List (Option Bool))
    (bits : List Bool) (right : List (Option Bool)) : Configuration :=
  eraseBlockFinish input before bits.reverse right

theorem eraseOutputBlock_runs (input : Tape) (before : List (Option Bool))
    (bits : List Bool) (right : List (Option Bool)) :
    RunsFor eraseOutputBlock (eraseOutputBlockStart input before bits right)
      (eraseOutputBlockFinish input before bits right) (4 * bits.length + 3) := by
  simpa [eraseOutputBlockStart, eraseOutputBlockFinish] using eraseBlock_run input before bits.reverse right

theorem eraseOutputBlock_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ eraseOutputBlock := by simp [eraseOutputBlock]

theorem eraseOutputBlock_control_closed (c d : Configuration)
    (hPc : c.pc < eraseOutputBlock.length) (step : Step eraseOutputBlock c d)
    (_hRunning : d.halted = false) : d.pc < eraseOutputBlock.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 5 at hPc
  change d.pc < 5
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, eraseOutputBlock,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem eraseOutputBlock_eval (input : Tape) (before : List (Option Bool))
    (bits : List Bool) (right : List (Option Bool)) :
    evalConfigWithin eraseOutputBlock (eraseOutputBlockStart input before bits right)
      (4 * bits.length + 3) = PMF.pure (eraseOutputBlockFinish input before bits right) :=
  (eraseOutputBlock_runs input before bits right).evalConfigWithin_eq_pure_of_no_randomBit
    eraseOutputBlock_no_randomBit

/-- Physical output cells of blocks ordered from nearest to farthest from
the current head. Empty blocks still have a real blank separator. This is
a specification of retained cells, not an operation on the machine. -/
def savedOutputBlocks : List (List Bool) → List (Option Bool)
  | [] => []
  | bits :: rest => bits.reverse.map some ++ none :: savedOutputBlocks rest

def eraseOutputBlocks : Nat → Program
  | 0 => [.halt]
  | count + 1 =>
      let tail := eraseOutputBlocks count
      eraseOutputBlock.asSubroutine 0 6 ++ tail.asSubroutine 6 (6 + tail.length + 1) ++ [.halt]

theorem eraseOutputBlocks_length (count : Nat) : (eraseOutputBlocks count).length = 8 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [eraseOutputBlocks, ih, Program.asSubroutine_length, eraseOutputBlock]; omega

def eraseOutputBlocksSteps : List (List Bool) → Nat
  | [] => 1
  | bits :: rest => (4 * bits.length + 3) + eraseOutputBlocksSteps rest + 1

def eraseOutputBlocksStart (input : Tape) (before : List (Option Bool))
    (blocks : List (List Bool)) (right : List (Option Bool)) : Configuration :=
  { inputTape := input, outputTape := { left := savedOutputBlocks blocks ++ before, right := right } }

def eraseOutputBlocksFinish (input : Tape) (before : List (Option Bool))
    (blocks : List (List Bool)) (right : List (Option Bool)) : Configuration :=
  { pc := 8 * blocks.length,
    inputTape := input,
    outputTape := {
      left := before
      right := List.replicate ((blocks.map List.length).sum + blocks.length) none ++ right },
    halted := true }

theorem eraseOutputBlocks_eval (input : Tape) (before : List (Option Bool))
    (blocks : List (List Bool)) (right : List (Option Bool)) :
    evalConfigWithin (eraseOutputBlocks blocks.length)
      (eraseOutputBlocksStart input before blocks right) (eraseOutputBlocksSteps blocks) =
      PMF.pure (eraseOutputBlocksFinish input before blocks right) := by
  induction blocks generalizing right with
  | nil =>
      simp [eraseOutputBlocks, eraseOutputBlocksStart, eraseOutputBlocksFinish,
        eraseOutputBlocksSteps, savedOutputBlocks, evalConfigWithin, stepPMF, next, Instruction.next]
  | cons bits rest ih =>
      let pre := eraseOutputBlock.asSubroutine 0 6
      let tail := eraseOutputBlocks rest.length
      let saved := savedOutputBlocks rest ++ before
      let middleRight := List.replicate (bits.length + 1) none ++ right
      let middle := eraseOutputBlocksStart input before rest middleRight
      have first := (eraseOutputBlock_runs input saved bits right).evalConfigWithin_withSubroutine_halted_of_closed
        [] eraseOutputBlock (tail.asSubroutine 6 (6 + tail.length + 1) ++ [.halt]) 6
        (by change 0 < 5; decide) rfl rfl eraseOutputBlock_control_closed eraseOutputBlock_no_randomBit
      have hFirstProgram : Program.withSubroutine [] eraseOutputBlock
          (tail.asSubroutine 6 (6 + tail.length + 1) ++ [.halt]) 6 = eraseOutputBlocks (bits :: rest).length := by
        simp [Program.withSubroutine, eraseOutputBlocks, tail, List.append_assoc]
      rw [hFirstProgram] at first
      have hEntry : (eraseOutputBlockFinish input saved bits right).resumeAt 6 = middle.rebasePc pre.length := by
        simp [eraseOutputBlockFinish, eraseBlockFinish, middle, middleRight, pre,
          eraseOutputBlocksStart, saved, Configuration.resumeAt, Configuration.rebasePc,
          Program.asSubroutine_length, eraseOutputBlock]
      have hInitial : eraseOutputBlockStart input saved bits right =
          eraseOutputBlocksStart input before (bits :: rest) right := by
        simp [eraseOutputBlockStart, eraseBlockState, saved, eraseOutputBlocksStart,
          savedOutputBlocks, List.append_assoc]
      simp only [List.length_nil] at first
      have hZero (c : Configuration) : c.rebasePc 0 = c := by
        cases c; simp [Configuration.rebasePc]
      rw [hZero] at first
      rw [hInitial, hEntry] at first
      have hTailHalts : ∀ c, PaddedRunsFor tail middle c (eraseOutputBlocksSteps rest) → c.halted = true := by
        intro c run
        have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
        change c ∈ (evalConfigWithin (eraseOutputBlocks rest.length)
          (eraseOutputBlocksStart input before rest middleRight) (eraseOutputBlocksSteps rest)).support at hc
        rw [ih] at hc
        have heq : c = eraseOutputBlocksFinish input before rest middleRight := by simpa using hc
        rw [heq]; rfl
      have second := Program.evalConfigWithin_withSubroutine_final_halt pre tail middle
        (by change 0 ≤ tail.length; omega) rfl (eraseOutputBlocksSteps rest) hTailHalts
      have hProgram : Program.withSubroutine pre tail [.halt] (pre.length + tail.length + 1) =
          eraseOutputBlocks (bits :: rest).length := by
        simp [Program.withSubroutine, pre, tail, eraseOutputBlocks,
          Program.asSubroutine_length, eraseOutputBlock]
      dsimp only at second
      rw [hProgram] at second
      change evalConfigWithin (eraseOutputBlocks (bits :: rest).length) (middle.rebasePc pre.length)
        (eraseOutputBlocksSteps rest + 1) = _ at second
      rw [eraseOutputBlocksSteps, Nat.add_assoc, evalConfigWithin_add, first, PMF.pure_bind, second]
      change (evalConfigWithin (eraseOutputBlocks rest.length)
        (eraseOutputBlocksStart input before rest middleRight) (eraseOutputBlocksSteps rest)).map _ = _
      rw [ih]
      have hPadding : List.replicate ((rest.map List.length).sum + rest.length) (none : Option Bool) ++ middleRight =
          List.replicate (((bits :: rest).map List.length).sum + (bits :: rest).length) none ++ right := by
        dsimp only [middleRight]
        rw [← List.append_assoc, List.replicate_append_replicate]
        congr 2
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      simp only [PMF.pure_map, eraseOutputBlocksFinish, hPadding]
      simp [pre, tail,
        eraseOutputBlocks_length, eraseOutputBlock, Program.asSubroutine_length,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      congr 1
      congr 1
      omega

theorem eraseOutputBlocks_haltsFrom (input : Tape) (before : List (Option Bool))
    (blocks : List (List Bool)) (right : List (Option Bool)) :
    ∀ c, PaddedRunsFor (eraseOutputBlocks blocks.length)
      (eraseOutputBlocksStart input before blocks right) c (eraseOutputBlocksSteps blocks) → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [eraseOutputBlocks_eval] at hc
  have heq : c = eraseOutputBlocksFinish input before blocks right := by simpa using hc
  rw [heq]; rfl

theorem eraseOutputBlocks_steps (blocks : List (List Bool)) :
    eraseOutputBlocksSteps blocks = 4 * ((blocks.map List.length).sum + blocks.length) + 1 := by
  induction blocks with
  | nil => rfl
  | cons bits rest ih => simp [eraseOutputBlocksSteps, ih]; omega

theorem eraseOutputBlocks_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (input : Tape) (before : List (Option Bool))
    (blocks : List (List Bool)) (right : List (Option Bool))
    (hLayout : ∀ pc, pc ≤ (eraseOutputBlocks blocks.length).length → pre.length + pc ≠ returnPc) :
    evalReturnWithin (Program.withSubroutine pre (eraseOutputBlocks blocks.length) suffix returnPc) returnPc
      ((eraseOutputBlocksStart input before blocks right).rebasePc pre.length) (eraseOutputBlocksSteps blocks) =
      PMF.pure ((eraseOutputBlocksFinish input before blocks right).resumeAt returnPc) := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre (eraseOutputBlocks blocks.length) suffix
    returnPc hLayout (eraseOutputBlocksStart input before blocks right)
    (by change 0 ≤ (eraseOutputBlocks blocks.length).length; omega) rfl (eraseOutputBlocksSteps blocks)
    (eraseOutputBlocks_haltsFrom input before blocks right), eraseOutputBlocks_eval, PMF.pure_map]

end Machine
