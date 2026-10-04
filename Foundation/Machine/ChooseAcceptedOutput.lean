import Foundation.Machine.ChooseResponsePrefix
import Foundation.Machine.GuardedTransfer
import Foundation.Machine.GuardedOutput

namespace Machine.ChooseAcceptedOutput

open GuardedCompiler

private def copyEntry : Nat := ChooseResponsePrefix.program.length + 1
private def finalPc : Nat := copyEntry + copyBitstring.length + 1
private def first : Program := ChooseResponsePrefix.program.asSubroutine 0 copyEntry

/-- Once the acceptance checks have succeeded and the original request has
been restored, copy its entire response into the result tape. This code
preserves the arbitrary trailing adversary state. It does not validate the
response itself and must only be chosen by the enclosing acceptance branch. -/
def program : Program := Program.withSubroutine first copyBitstring [.halt] finalPc

private theorem first_layout : program =
    Program.withSubroutine [] ChooseResponsePrefix.program
      (copyBitstring.asSubroutine copyEntry finalPc ++ [.halt]) copyEntry := by
  simp [program, first, copyEntry, Program.withSubroutine, Program.asSubroutine_length]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = first.length + copyBitstring.length + 1 + 0 := by
      simp [finalPc, copyEntry, first, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Native response-copy correctness for an arbitrary finite response,
including every state bit after its two candidate fields. -/
theorem runs_valid (n : Nat) (instanceBits reply : List Bool) :
    ∃ target used,
      RunsFor program
        (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply)) target used ∧
      target.halted = true ∧ target.outputBits = reply := by
  let before := some false :: List.replicate reply.length (some true) ++ instanceBits.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
  obtain ⟨prepared, u₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ := ChooseResponsePrefix.runs_valid n instanceBits reply
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted
    [] ChooseResponsePrefix.program (copyBitstring.asSubroutine copyEntry finalPc ++ [.halt])
    copyEntry (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame reply))
      (prepared.resumeAt copyEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  have run₂ := copyScratch_runs before [] reply 0
  obtain ⟨v₂, _, embedded₂⟩ := run₂.withSubroutine_halted
    first copyBitstring [.halt] finalPc (Nat.zero_le _) rfl rfl
  have hPacked := packedLogicalInput_equivalent reply
  have hCall : ((copyScratchStart before [] reply 0).rebasePc first.length).Equivalent
      (prepared.resumeAt copyEntry) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · change 0 + first.length = copyEntry
      simp [first, copyEntry, Program.asSubroutine_length]
    · change ({ packedLogicalInput reply with left := before } : Tape).Equivalent prepared.inputTape
      rw [hInput₁]
      exact ⟨hPacked.1, fun _ => rfl, hPacked.2.2⟩
    · exact hOutput₁.symm
  have r₂ : RunsFor program ((copyScratchStart before [] reply 0).rebasePc first.length)
      ((copyScratchFinish before [] reply 0).resumeAt finalPc) v₂ := embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂.exists_equivalent hCall
  have hPc : actual.pc = finalPc := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  have hBits : (copyScratchFinish before [] reply 0).outputBits = reply := by
    simp [copyScratchFinish, Configuration.outputBits, Tape.bits]
  refine ⟨{ actual with halted := true }, v₁+v₂+1,
    (r₁.trans actualRun₂).succ (final_step actual hPc hActive), rfl, ?_⟩
  exact hActual.2.2.2.symm.bits.trans hBits

/-- The copy branch also terminates on every malformed finite request.
Termination alone does not establish that a malformed response is accepted. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ 10000 * (raw.length+1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁⟩ := ChooseResponsePrefix.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] ChooseResponsePrefix.program (copyBitstring.asSubroutine copyEntry finalPc ++ [.halt])
    copyEntry (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt copyEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨copied, u₂, hu₂, run₂, hHalt₂⟩ := copyBitstring_terminates_from_anyTape prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first copyBitstring [.halt] finalPc (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt copyEntry) (copied.resumeAt finalPc) v₂ := by
    simpa [program, first, copyEntry, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt] using embedded₂
  have hStorage := sourceStorage_le_of_run run₁
  have hInitial : sourceStorage (Configuration.initial raw) ≤ raw.length+2 := by
    cases raw <;> simp [sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  refine ⟨{ copied.resumeAt finalPc with halted := true }, v₁+v₂+1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  simp only [sourceStorage] at hStorage hInitial
  dsimp only [ChooseResponsePrefix.budget] at hu₁
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (10000 * (raw.length+1)) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun m => 10000 * (m+1), (PolynomiallyBounded.const 10000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- Evaluator correctness at the uniform all-input time bound, rather than
at a trace-dependent fuel. The complete finite response is preserved. -/
theorem eval_valid (n : Nat) (instanceBits reply : List Bool) :
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    evalWithin program raw (10000*(raw.length+1)) = PMF.pure (some reply) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  obtain ⟨target, used, run, hHalt, hBits⟩ := runs_valid n instanceBits reply
  have hHalts : HaltsWith program raw reply used := ⟨target, run, hHalt, hBits⟩
  rw [evalWithin_eq_of_haltsWithin program raw (10000*(raw.length+1)) used
    (haltsWithin raw) (hHalts.haltsWithin_of_no_randomBit no_randomBit)]
  exact hHalts.evalWithin_eq_pure_of_no_randomBit no_randomBit

end Machine.ChooseAcceptedOutput
