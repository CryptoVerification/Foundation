import Foundation.Machine.OppositeCall

namespace Machine

/-- The finite subroutine relocation inserts only return jumps. It cannot
introduce random instructions into deterministic native source code. -/
theorem Program.asSubroutine_no_randomBit (source : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (base returnPc : Nat)
    (tape : TapeId) : Instruction.randomBit tape ∉ source.asSubroutine base returnPc := by
  simp only [Program.asSubroutine, List.mem_append, List.mem_map,
    List.mem_singleton, not_or]
  refine ⟨?_, by simp⟩
  rintro ⟨instruction, hMember, hInstruction⟩
  cases instruction <;> simp [Instruction.asSubroutine] at hInstruction
  exact h _ (hInstruction ▸ hMember)

theorem Program.swapTapes_no_randomBit (source : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ source.swapTapes := by
  simp only [Program.swapTapes, List.mem_map]
  rintro ⟨instruction, hMember, hInstruction⟩
  cases instruction <;> try simp [Instruction.swapTapes] at hInstruction
  rename_i which
  cases which <;> cases tape <;> simp [TapeId.swap] at hInstruction
  all_goals exact h _ hMember

namespace GuardedCompiler

private theorem body_no_randomBit (length pc : Nat) (instruction : Instruction)
    (h : ∀ tape, instruction ≠ Instruction.randomBit tape) (tape : TapeId) :
    Instruction.randomBit tape ∉ body length pc instruction := by
  cases instruction with
  | randomBit which => exact False.elim (h which rfl)
  | halt => simp [body]
  | jump target => simp [body]
  | branch which blankPc zeroPc onePc => simp [body, branchAt]
  | moveLeft which =>
      simp only [body, List.mem_append, not_or]
      refine ⟨by simp [leftAt], ?_⟩
      exact Program.asSubroutine_no_randomBit _
        (by intro selected; simp [VirtualCell.growLeftCell]) _ _ tape
  | moveRight which =>
      exact Program.asSubroutine_no_randomBit _
        (by intro selected; simp [VirtualCell.moveRightCell]) _ _ tape
  | write which bit =>
      exact Program.asSubroutine_no_randomBit _
        (by intro selected; cases bit <;> simp [VirtualCell.writeCell]) _ _ tape
  | erase which =>
      exact Program.asSubroutine_no_randomBit _
        (by intro selected; simp [VirtualCell.writeCell]) _ _ tape

theorem compile_no_randomBit (source : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ compile source := by
  have blocksNo (length pc : Nat) : Instruction.randomBit tape ∉ blocks length pc source := by
    induction source generalizing pc with
    | nil => simp [blocks]
    | cons instruction rest ih =>
        have hInstruction : ∀ selected, instruction ≠ Instruction.randomBit selected := by
          intro selected equal
          exact h selected (by simp [equal])
        have hRest : ∀ selected, Instruction.randomBit selected ∉ rest := by
          intro selected member
          exact h selected (List.mem_cons_of_mem _ member)
        simp only [blocks, block, List.mem_append, not_or]
        exact ⟨⟨body_no_randomBit length pc instruction hInstruction tape, by simp⟩, ih hRest (pc + 1)⟩
  simpa [compile] using blocksNo source.length 0

theorem rawCompile_no_randomBit (source : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ rawCompile source := by
  simp only [rawCompile, Program.withSubroutine, List.mem_append, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Program.asSubroutine_no_randomBit _ prepareTapes_no_randomBit _ _ tape
  · exact Program.asSubroutine_no_randomBit _ (compile_no_randomBit source h) _ _ tape
  · exact ⟨Program.asSubroutine_no_randomBit _ extractOutput_no_randomBit _ _ tape, by simp⟩

theorem rawCompileOpposite_no_randomBit (source : Program)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ rawCompileOpposite source :=
  Program.swapTapes_no_randomBit _ (rawCompile_no_randomBit source h) tape

/-- A deterministic guarded call has one returned physical configuration.
Its logical source output agrees with the existing standalone evaluator;
this lemma performs no tape preparation outside the compiled native code. -/
theorem rawCompileOpposite_result (source : Program) (input output : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ source)
    (halts : HaltsWithin source input (q input.length))
    (correct : evalWithin source input (q input.length) = PMF.pure (some output)) :
    ∃ c : Configuration, c.halted = true ∧ c.outputBits = output ∧
      evalConfigWithin (rawCompileOpposite source)
        (packInputStart beforeInput beforeOutput input).swapTapes (rawTraceBudget q input.length) =
        PMF.pure (rawResultFrom source input beforeInput beforeOutput c).swapTapes := by
  have layout := (preparedSource_equivalent_initial input).symm
  have stopped := halts.of_equivalent_initial layout
  obtain ⟨c, used, hUsed, run, hHalted⟩ :=
    exists_halted_run_of_haltsFrom source (preparedSource input) (q input.length) stopped
  have allStopped := run.haltsFrom_of_no_randomBit hHalted hNoRandom (Nat.le_refl used)
  have hEval : evalConfigWithin source (preparedSource input) (q input.length) = PMF.pure c := by
    rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed allStopped]
    exact run.evalConfigWithin_eq_pure_of_no_randomBit hNoRandom
  have observed := (preparedSource_equivalent_initial input).evalOutput source (q input.length)
  change (evalConfigWithin source (preparedSource input) (q input.length)).map
    (fun c => if c.halted then some c.outputBits else none) = evalWithin source input (q input.length) at observed
  rw [hEval, PMF.pure_map, hHalted, if_pos rfl, correct] at observed
  have hOutput : c.outputBits = output := by
    have member : some c.outputBits ∈ (PMF.pure (some output)).support := by
      rw [← observed]; simp
    simpa using member
  refine ⟨c, hHalted, hOutput, ?_⟩
  rw [rawCompileOpposite_configuration_eval source input beforeInput beforeOutput q halts,
    hEval, PMF.pure_map]

end GuardedCompiler

/-- Link an existing operational trace into its actual caller, retaining
both physical tapes. All source transitions are charged; no fresh input or
abstract whole-string operation is inserted by this trace theorem. -/
theorem nativeCall_of_eval (pre source suffix : Program) (returnPc : Nat)
    (canonical returned actual : Configuration) (limit : Nat)
    (hPc : canonical.pc ≤ source.length) (hActive : canonical.halted = false)
    (hHalted : returned.halted = true)
    (hEval : evalConfigWithin source canonical limit = PMF.pure returned)
    (hLayout : (canonical.rebasePc pre.length).Equivalent actual) :
    ∃ (target : Configuration) (used : Nat), used ≤ limit ∧
      RunsFor (Program.withSubroutine pre source suffix returnPc) actual target used ∧
      (returned.resumeAt returnPc).Equivalent target := by
  have padded : PaddedRunsFor source canonical returned limit := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [hEval]
    simp
  obtain ⟨sourceSteps, hSourceSteps, sourceRun⟩ := padded.toRunsFor_le
  obtain ⟨used, hUsed, embedded⟩ := sourceRun.withSubroutine_halted pre source suffix returnPc
    hPc hActive hHalted
  obtain ⟨target, hRun, hTarget⟩ := embedded.exists_equivalent hLayout
  exact ⟨target, used, hUsed.trans hSourceSteps, hRun, hTarget⟩

end Machine
