import Foundation.Machine.ChoosePowerDispatch
import Foundation.Machine.GuardedTrace

namespace Machine.ChooseCheckContinuation

private def acceptReset : Nat := 6
private def acceptBody : Nat := acceptReset + ChoosePowerReset.program.length + 1
private def rejectReset (accept : Program) : Nat := acceptBody + accept.length + 1
private def rejectBody (accept : Program) : Nat := rejectReset accept + ChoosePowerReset.program.length + 1
private def finalPc (accept reject : Program) : Nat := rejectBody accept + reject.length + 1
private def selector (accept : Program) : Program :=
  ChoosePowerDispatch.dispatch acceptReset (rejectReset accept)
private def tail (accept reject : Program) : Program :=
  ChoosePowerReset.program.asSubroutine acceptReset acceptBody ++
    accept.asSubroutine acceptBody (finalPc accept reject) ++
      ChoosePowerReset.program.asSubroutine (rejectReset accept) (rejectBody accept) ++
        reject.asSubroutine (rejectBody accept) (finalPc accept reject) ++ [.halt]

/-- Inspect the actual returned decision, recover the protected original
request using real erasure and rewind, and execute the selected continuation.
Each branch has its own reset so the decision stays in finite control. -/
def program (accept reject : Program) : Program := selector accept ++ tail accept reject

private def resetEntry (accept : Program) (status : Bool) : Nat :=
  if status then acceptReset else rejectReset accept
private def bodyEntry (accept : Program) (status : Bool) : Nat :=
  if status then acceptBody else rejectBody accept
private def resetPrefix (accept reject : Program) (status : Bool) : Program :=
  if status then selector accept else
    selector accept ++ ChoosePowerReset.program.asSubroutine acceptReset acceptBody ++
      accept.asSubroutine acceptBody (finalPc accept reject)
private def resetSuffix (accept reject : Program) (status : Bool) : Program :=
  if status then
    accept.asSubroutine acceptBody (finalPc accept reject) ++
      ChoosePowerReset.program.asSubroutine (rejectReset accept) (rejectBody accept) ++
        reject.asSubroutine (rejectBody accept) (finalPc accept reject) ++ [.halt]
  else reject.asSubroutine (rejectBody accept) (finalPc accept reject) ++ [.halt]
private def bodyPrefix (accept reject : Program) (status : Bool) : Program :=
  resetPrefix accept reject status ++
    ChoosePowerReset.program.asSubroutine (resetEntry accept status) (bodyEntry accept status)
private def bodySuffix (accept reject : Program) (status : Bool) : Program :=
  if status then
    ChoosePowerReset.program.asSubroutine (rejectReset accept) (rejectBody accept) ++
      reject.asSubroutine (rejectBody accept) (finalPc accept reject) ++ [.halt]
  else [.halt]

private theorem resetPrefix_length (accept reject : Program) (status : Bool) :
    (resetPrefix accept reject status).length = resetEntry accept status := by
  cases status <;> simp [resetPrefix, resetEntry, selector, ChoosePowerDispatch.dispatch,
    acceptReset, rejectReset, acceptBody, Program.asSubroutine_length] <;> omega

private theorem bodyPrefix_length (accept reject : Program) (status : Bool) :
    (bodyPrefix accept reject status).length = bodyEntry accept status := by
  cases status <;> simp [bodyPrefix, resetPrefix, resetEntry, bodyEntry, selector,
    ChoosePowerDispatch.dispatch, acceptReset, rejectReset, acceptBody, rejectBody,
    Program.asSubroutine_length, Nat.add_assoc] <;> omega

private theorem reset_layout (accept reject : Program) (status : Bool) :
    program accept reject = Program.withSubroutine (resetPrefix accept reject status)
      ChoosePowerReset.program (resetSuffix accept reject status) (bodyEntry accept status) := by
  unfold Program.withSubroutine
  rw [resetPrefix_length]
  cases status <;> simp [program, tail, resetPrefix, resetSuffix, bodyEntry,
    resetEntry, List.append_assoc]

private theorem body_layout (accept reject : Program) (status : Bool) :
    program accept reject = Program.withSubroutine (bodyPrefix accept reject status)
      (if status then accept else reject) (bodySuffix accept reject status) (finalPc accept reject) := by
  unfold Program.withSubroutine
  rw [bodyPrefix_length]
  cases status <;> simp [program, tail, bodyPrefix, resetPrefix, resetEntry, bodyEntry,
    bodySuffix, List.append_assoc]

private theorem final_step (accept reject : Program) (c : Configuration)
    (hPc : c.pc = finalPc accept reject) (hActive : c.halted = false) :
    Step (program accept reject) c { c with halted := true } := by
  have hLookup : (program accept reject)[finalPc accept reject]? = some .halt := by
    rw [body_layout accept reject false]
    change (Program.withSubroutine (bodyPrefix accept reject false) reject [.halt]
      (finalPc accept reject))[finalPc accept reject]? = some .halt
    have hIndex : finalPc accept reject =
        (bodyPrefix accept reject false).length + reject.length + 1 + 0 := by
      simp [bodyPrefix_length, bodyEntry, finalPc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The selected continuation receives the same complete original request,
including its arbitrary state suffix. No decoder or newly loaded tape is
used to restore it. The source decision and guarded scratch are removed by
actual instructions before the continuation executes. -/
theorem runs_returned (core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status])
    (accept reject : Program) (next : Configuration) (nextUsed : Nat)
    (nextRun : RunsFor (if status then accept else reject)
      (Configuration.initial request) next nextUsed)
    (nextHalt : next.halted = true) :
    let returned := ((GuardedCompiler.rawResultFrom core columns [none]
      (none :: request.reverse.map some) c).swapTapes).resumeAt 0
    ∃ target used,
      used ≤ 4 + eraseOutputBlocksSteps [[status],
        GuardedCompiler.storedSourceScratchBits columns c.inputTape] + 7 +
          (2 * request.length + 4) + 1 + nextUsed + 1 ∧
      RunsFor (program accept reject) returned target used ∧
      target.halted = true ∧ target.outputBits = next.outputBits := by
  dsimp only
  let returned := ((GuardedCompiler.rawResultFrom core columns [none]
    (none :: request.reverse.map some) c).swapTapes).resumeAt 0
  obtain ⟨d, hd, dispatchRun⟩ := ChoosePowerDispatch.runs_returned core columns request
    c status hStatus acceptReset (rejectReset accept) (tail accept reject)
  have firstRun : RunsFor (program accept reject) returned
      (returned.resumeAt (resetEntry accept status)) d := by
    simpa [program, selector, resetEntry, returned] using dispatchRun
  obtain ⟨restored, u, hu, resetRun, resetHalt, hRestored⟩ :=
    ChoosePowerReset.runs_returned core columns request c status hStatus
  obtain ⟨v, hv, resetEmbedded⟩ := resetRun.withSubroutine_halted
    (resetPrefix accept reject status) ChoosePowerReset.program
    (resetSuffix accept reject status) (bodyEntry accept status)
    (Nat.zero_le _) rfl resetHalt
  have secondRun : RunsFor (program accept reject)
      (returned.resumeAt (resetEntry accept status))
      (restored.resumeAt (bodyEntry accept status)) v := by
    rw [reset_layout accept reject status]
    simpa [returned, resetPrefix_length, Configuration.rebasePc, Configuration.resumeAt]
      using resetEmbedded
  obtain ⟨w, hw, nextEmbedded⟩ := nextRun.withSubroutine_halted
    (bodyPrefix accept reject status) (if status then accept else reject)
    (bodySuffix accept reject status) (finalPc accept reject)
    (Nat.zero_le _) rfl nextHalt
  have canonicalRun : RunsFor (program accept reject)
      ((Configuration.initial request).rebasePc (bodyEntry accept status))
      (next.resumeAt (finalPc accept reject)) w := by
    rw [body_layout accept reject status]
    simpa only [bodyPrefix_length] using nextEmbedded
  have hCall : ((Configuration.initial request).rebasePc (bodyEntry accept status)).Equivalent
      (restored.resumeAt (bodyEntry accept status)) :=
    ⟨rfl, rfl, hRestored.2.2.1.symm, hRestored.2.2.2.symm⟩
  obtain ⟨actual, actualRun, hActual⟩ := canonicalRun.exists_equivalent hCall
  have hPc : actual.pc = finalPc accept reject := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, d + v + w + 1, by omega,
    ((firstRun.trans secondRun).trans actualRun).succ
      (final_step accept reject actual hPc hActive), rfl, ?_⟩
  exact hActual.2.2.2.symm.bits

/-- Branch selection, erasure, and rewind introduce no random instructions. -/
theorem no_randomBit (accept reject : Program)
    (hAccept : ∀ tape, Instruction.randomBit tape ∉ accept)
    (hReject : ∀ tape, Instruction.randomBit tape ∉ reject) (tape : TapeId) :
    Instruction.randomBit tape ∉ program accept reject := by
  have hSelector : Instruction.randomBit tape ∉ selector accept := by
    cases tape <;> simp [selector, ChoosePowerDispatch.dispatch]
  have h₁ := Program.asSubroutine_no_randomBit ChoosePowerReset.program
    ChoosePowerReset.no_randomBit acceptReset acceptBody tape
  have h₂ := Program.asSubroutine_no_randomBit accept hAccept acceptBody (finalPc accept reject) tape
  have h₃ := Program.asSubroutine_no_randomBit ChoosePowerReset.program
    ChoosePowerReset.no_randomBit (rejectReset accept) (rejectBody accept) tape
  have h₄ := Program.asSubroutine_no_randomBit reject hReject (rejectBody accept) (finalPc accept reject) tape
  simpa only [program, tail, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or] using
    And.intro hSelector (And.intro (And.intro (And.intro (And.intro h₁ h₂) h₃) h₄)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp))

private def postEntry (check : Program) : Nat := check.length + 1
private def outerFinal (check accept reject : Program) : Nat :=
  postEntry check + (program accept reject).length + 1
private def beforePost (check : Program) : Program := check.asSubroutine 0 (postEntry check)

/-- Connect a native check to decision, physical request recovery, and its
selected continuation in one finite program. The check still has to prove
its own real returned layout and stopping bound. -/
def withCheck (check accept reject : Program) : Program :=
  Program.withSubroutine (beforePost check) (program accept reject) [.halt]
    (outerFinal check accept reject)

private theorem check_layout (check accept reject : Program) :
    withCheck check accept reject = Program.withSubroutine [] check
      ((program accept reject).asSubroutine (postEntry check) (outerFinal check accept reject) ++ [.halt])
      (postEntry check) := by
  simp [withCheck, beforePost, Program.withSubroutine, postEntry]

private theorem outer_final_step (check accept reject : Program) (actual : Configuration)
    (hPc : actual.pc = outerFinal check accept reject) (hActive : actual.halted = false) :
    Step (withCheck check accept reject) actual { actual with halted := true } := by
  have hLookup : (withCheck check accept reject)[outerFinal check accept reject]? = some .halt := by
    have hIndex : outerFinal check accept reject = (beforePost check).length +
        (program accept reject).length + 1 + 0 := by
      simp [outerFinal, beforePost, postEntry, Program.asSubroutine_length]
    unfold withCheck
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- The whole check-and-branch code follows the actual check trace. Its
layout premise is supplied by a saved width/range call or a framed subgroup
call; it is not an assumption that a new tape may be installed for free. -/
theorem runs_withCheck (check core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status])
    (checked : Configuration) (checkUsed : Nat)
    (checkRun : RunsFor check (Configuration.initial request) checked checkUsed)
    (checkHalt : checked.halted = true)
    (checkReturned : (checked.resumeAt 0).Equivalent
      (((GuardedCompiler.rawResultFrom core columns [none]
        (none :: request.reverse.map some) c).swapTapes).resumeAt 0))
    (accept reject : Program) (next : Configuration) (nextUsed : Nat)
    (nextRun : RunsFor (if status then accept else reject)
      (Configuration.initial request) next nextUsed)
    (nextHalt : next.halted = true) :
    ∃ target used,
      used ≤ checkUsed + (4 + eraseOutputBlocksSteps [[status],
        GuardedCompiler.storedSourceScratchBits columns c.inputTape] + 7 +
          (2 * request.length + 4) + 1 + nextUsed + 1) + 1 ∧
      RunsFor (withCheck check accept reject) (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits = next.outputBits := by
  obtain ⟨u, hu, checkEmbedded⟩ := checkRun.withSubroutine_halted [] check
    ((program accept reject).asSubroutine (postEntry check) (outerFinal check accept reject) ++ [.halt])
    (postEntry check) (Nat.zero_le _) rfl checkHalt
  have firstRun : RunsFor (withCheck check accept reject) (Configuration.initial request)
      (checked.resumeAt (postEntry check)) u := by
    rw [check_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using checkEmbedded
  obtain ⟨postTarget, postUsed, hPostUsed, postRun, postHalt, postBits⟩ :=
    runs_returned core columns request c status hStatus accept reject next nextUsed nextRun nextHalt
  obtain ⟨v, hv, postEmbedded⟩ := postRun.withSubroutine_halted (beforePost check)
    (program accept reject) [.halt] (outerFinal check accept reject)
    (Nat.zero_le _) rfl postHalt
  let returned := ((GuardedCompiler.rawResultFrom core columns [none]
    (none :: request.reverse.map some) c).swapTapes).resumeAt 0
  have canonicalRun : RunsFor (withCheck check accept reject)
      (returned.rebasePc (beforePost check).length)
      (postTarget.resumeAt (outerFinal check accept reject)) v := postEmbedded
  have hCall : (returned.rebasePc (beforePost check).length).Equivalent
      (checked.resumeAt (postEntry check)) := by
    refine ⟨?_, rfl, checkReturned.2.2.1.symm, checkReturned.2.2.2.symm⟩
    simp [returned, Configuration.rebasePc, Configuration.resumeAt, beforePost,
      postEntry, Program.asSubroutine_length]
  obtain ⟨actual, actualRun, hActual⟩ := canonicalRun.exists_equivalent hCall
  have hPc : actual.pc = outerFinal check accept reject := by
    simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, u + v + 1, by omega,
    (firstRun.trans actualRun).succ (outer_final_step check accept reject actual hPc hActive), rfl, ?_⟩
  exact hActual.2.2.2.symm.bits.trans postBits

/-- Charge scratch erasure to storage actually produced by the check.
One transition adds at most one tape cell; no separately assumed scratch
bound is needed for the selected continuation's polynomial budget. -/
theorem runs_withCheck_bounded (check core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status])
    (checked : Configuration) (checkUsed : Nat)
    (checkRun : RunsFor check (Configuration.initial request) checked checkUsed)
    (checkHalt : checked.halted = true)
    (checkReturned : (checked.resumeAt 0).Equivalent
      (((GuardedCompiler.rawResultFrom core columns [none]
        (none :: request.reverse.map some) c).swapTapes).resumeAt 0))
    (accept reject : Program) (next : Configuration) (nextUsed : Nat)
    (nextRun : RunsFor (if status then accept else reject)
      (Configuration.initial request) next nextUsed)
    (nextHalt : next.halted = true) :
    ∃ target used,
      used ≤ 5 * checkUsed + 6 * request.length + nextUsed + 40 ∧
      RunsFor (withCheck check accept reject) (Configuration.initial request) target used ∧
      target.halted = true ∧ target.outputBits = next.outputBits := by
  have hScratch := ChoosePowerReset.scratch_length_le_returned_outputBits
    core columns request c status hStatus
  have hBits := checkReturned.outputBits
  have hCells := Tape.bits_length_le_cells checked.outputTape
  have hStorage := GuardedCompiler.sourceStorage_le_of_run checkRun
  have hInitial := GuardedCompiler.initial_sourceStorage_le request
  have hScratchBound :
      (GuardedCompiler.storedSourceScratchBits columns c.inputTape).length ≤
        request.length + 2 + checkUsed := by
    rw [← hBits] at hScratch
    simp only [Configuration.resumeAt, Configuration.outputBits] at hScratch
    unfold GuardedCompiler.sourceStorage at hStorage hInitial
    omega
  obtain ⟨target, used, hUsed, run, hHalt, hOutput⟩ :=
    runs_withCheck check core columns request c status hStatus checked checkUsed
      checkRun checkHalt checkReturned accept reject next nextUsed nextRun nextHalt
  refine ⟨target, used, ?_, run, hHalt, hOutput⟩
  simp only [eraseOutputBlocksSteps, List.length_cons, List.length_nil] at hUsed
  omega

/-- Native deterministic checks and continuations remain deterministic
when connected through the finite decision-and-reset code. -/
theorem withCheck_no_randomBit (check accept reject : Program)
    (hCheck : ∀ tape, Instruction.randomBit tape ∉ check)
    (hAccept : ∀ tape, Instruction.randomBit tape ∉ accept)
    (hReject : ∀ tape, Instruction.randomBit tape ∉ reject) (tape : TapeId) :
    Instruction.randomBit tape ∉ withCheck check accept reject := by
  have h₁ := Program.asSubroutine_no_randomBit check hCheck 0 (postEntry check) tape
  have h₂ := Program.asSubroutine_no_randomBit (program accept reject)
    (no_randomBit accept reject hAccept hReject) (beforePost check).length
    (outerFinal check accept reject) tape
  simpa only [withCheck, beforePost, Program.withSubroutine, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or] using
    And.intro (And.intro h₁ h₂)
      (show Instruction.randomBit tape ≠ Instruction.halt by cases tape <;> simp)

end Machine.ChooseCheckContinuation
