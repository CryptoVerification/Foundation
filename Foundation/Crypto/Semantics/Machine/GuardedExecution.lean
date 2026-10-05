import Foundation.Crypto.Semantics.Machine.GuardedTrace
import Foundation.Crypto.Semantics.Machine.SubroutineProbability
import Foundation.Crypto.Semantics.Machine.GuardedTransfer

namespace Machine.GuardedCompiler

private theorem evalConfigWithin_of_halted (p : Program) (c : Configuration)
    (hHalt : c.halted = true) (steps : Nat) :
    evalConfigWithin p c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, hHalt]

/-- When every source branch has halted by `steps`, the expanded machine
has exactly the represented source distribution at any target budget above
the displayed bound. Every physical transition of each expanded block is
counted, including frontier growth. Both entry tapes must already have their
guarded representations; this theorem does not prepare raw input or extract
raw output for free. -/
theorem compile_eval_of_all_branches_halted (source : Program) (steps : Nat)
    (c : Configuration)
    (hHalt : ∀ d, PaddedRunsFor source c d steps → d.halted = true)
    (budget : Nat)
    (hBudget : steps * (17 * (sourceStorage c + steps) + 23) ≤ budget)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput c) budget =
      (evalConfigWithin source c steps).map
        (encodeConfiguration source.length beforeInput beforeOutput) := by
  induction steps generalizing c budget with
  | zero =>
      have hc := hHalt c (PaddedRunsFor.zero c)
      simp only [evalConfigWithin, PMF.pure_map]
      exact evalConfigWithin_of_halted (compile source)
        (encodeConfiguration source.length beforeInput beforeOutput c) hc budget
  | succ steps ih =>
      cases hActive : c.halted with
      | true =>
          rw [evalConfigWithin_of_halted source c hActive,
            evalConfigWithin_of_halted (compile source)
              (encodeConfiguration source.length beforeInput beforeOutput c) hActive,
            PMF.pure_map]
      | false =>
          have hCost := blockSteps_le source c
          change blockSteps source c ≤ 17 * sourceStorage c + 23 at hCost
          have hFits : blockSteps source c ≤ budget := by
            have hLarger : 17 * sourceStorage c + 23 ≤
                17 * (sourceStorage c + (steps + 1)) + 23 := by omega
            have hAtLeast : 17 * (sourceStorage c + (steps + 1)) + 23 ≤
                (steps + 1) * (17 * (sourceStorage c + (steps + 1)) + 23) :=
              Nat.le_mul_of_pos_left _ (by omega)
            exact hCost.trans (hLarger.trans (hAtLeast.trans hBudget))
          have hSplit : budget = blockSteps source c + (budget - blockSteps source c) := by omega
          rw [hSplit, evalConfigWithin_add,
            compile_step_eval source c hActive beforeInput beforeOutput,
            PMF.bind_map, evalConfigWithin_succ_head, PMF.map_bind]
          rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
          congr 1
          funext d hd
          have hPadded : PaddedStep source c d := (mem_support_stepPMF_iff source c d).mp hd
          have hStep : Step source c d := by
            rcases hPadded with hStep | ⟨hStopped, _⟩
            · exact hStep
            · simp [hActive] at hStopped
          have hStorage := sourceStorage_le_of_step hStep
          have hRemainder : steps * (17 * (sourceStorage d + steps) + 23) ≤
              budget - blockSteps source c := by
            calc
              _ ≤ steps * (17 * (sourceStorage c + (steps + 1)) + 23) :=
                Nat.mul_le_mul_left steps (by omega)
              _ ≤ budget - blockSteps source c := by
                rw [Nat.succ_mul] at hBudget
                omega
          apply ih d
          · intro finish run
            apply hHalt finish
            simpa [Nat.add_comm] using
              (PaddedRunsFor.succ (PaddedRunsFor.zero c) (Or.inl hStep)).trans run
          · exact hRemainder

/-- Every compiled random branch, not merely a selected matching trace,
halts at the polynomial simulation bound from a represented source state. -/
theorem compile_all_branches_halted (source : Program) (steps : Nat) (c : Configuration)
    (hHalt : ∀ d, PaddedRunsFor source c d steps → d.halted = true)
    (budget : Nat) (hBudget : steps * (17 * (sourceStorage c + steps) + 23) ≤ budget)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∀ final, PaddedRunsFor (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput c) final budget →
      final.halted = true := by
  intro final run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [compile_eval_of_all_branches_halted source steps c hHalt budget hBudget
    beforeInput beforeOutput, PMF.mem_support_map_iff] at hMem
  obtain ⟨d, hd, rfl⟩ := hMem
  exact hHalt d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hd)

/-- Fresh source inputs may be simulated from their explicitly represented
initial configurations with the existing polynomial `traceBudget`.
Operational input preparation and output extraction remain separate work. -/
theorem compile_initial_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (hHalt : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
      (traceBudget q input.length) =
      (evalConfigWithin source (Configuration.initial input) (q input.length)).map
        (encodeConfiguration source.length beforeInput beforeOutput) := by
  apply compile_eval_of_all_branches_halted
  · exact hHalt
  · apply Nat.mul_le_mul_left
    have hStorage := initial_sourceStorage_le input
    omega

theorem compile_initial_all_branches_halted (source : Program) (input : List Bool)
    (q : Nat → Nat) (hHalt : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) :
    ∀ final, PaddedRunsFor (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
      final (traceBudget q input.length) → final.halted = true := by
  apply compile_all_branches_halted
  · exact hHalt
  · apply Nat.mul_le_mul_left
    have hStorage := initial_sourceStorage_le input
    omega

/-- The prepared logical tapes retain outer blanks. Their storage is
bounded explicitly instead of replacing them with canonical tapes for free. -/
theorem preparedSource_sourceStorage_le (input : List Bool) :
    sourceStorage (preparedSource input) ≤ 2 * input.length + 2 := by
  cases input with
  | nil => simp [sourceStorage, preparedSource, packedLogicalInput_nil,
      rewoundTape, Tape.cells]
  | cons bit rest =>
      simp [sourceStorage, preparedSource, packedLogicalInput_cons,
        rewound_blank_region, Tape.cells]
      omega

def preparedTraceBudget (q : Nat → Nat) (m : Nat) : Nat :=
  q m * (17 * (2 * m + 2 + q m) + 23)

theorem preparedTraceBudget_polynomiallyBounded {q : Nat → Nat}
    (h : PolynomiallyBounded q) : PolynomiallyBounded (preparedTraceBudget q) :=
  h.mul (((PolynomiallyBounded.const 17).mul
    ((((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 2)).add h)).add (PolynomiallyBounded.const 23))

/-- Guarded execution from the tapes actually constructed by the input
preparation routine has the full represented source distribution. -/
theorem compile_prepared_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (preparedSource input))
      (preparedTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (encodeConfiguration source.length beforeInput beforeOutput) := by
  apply compile_eval_of_all_branches_halted
  · exact preparedSource_all_branches_halted source input _ halts
  · apply Nat.mul_le_mul_left
    have hStorage := preparedSource_sourceStorage_le input
    omega

theorem compile_prepared_all_branches_halted (source : Program) (input : List Bool)
    (q : Nat → Nat) (halts : HaltsWithin source input (q input.length))
    (beforeInput beforeOutput : List (Option Bool)) :
    ∀ final, PaddedRunsFor (compile source)
      (encodeConfiguration source.length beforeInput beforeOutput (preparedSource input))
      final (preparedTraceBudget q input.length) → final.halted = true := by
  apply compile_all_branches_halted
  · exact preparedSource_all_branches_halted source input _ halts
  · apply Nat.mul_le_mul_left
    have hStorage := preparedSource_sourceStorage_le input
    omega

/-- Finite code that prepares both guarded tapes, calls the rebased
expanded source, and halts after its return. It still exposes the encoded
output region: this is not yet the compiler with raw-output extraction. -/
def initializedCompile (source : Program) : Program :=
  Program.withSubroutine (prepareTapes.asSubroutine 0 87) (compile source) [.halt]
    (87 + (compile source).length + 1)

private theorem initializedCompile_halt_instruction (source : Program) :
    (initializedCompile source)[87 + (compile source).length + 1]? = some .halt := by
  let pre := prepareTapes.asSubroutine 0 87
  have hPre : pre.length = 87 := rfl
  change (Program.withSubroutine pre (compile source) [.halt]
    (87 + (compile source).length + 1))[87 + (compile source).length + 1]? = some .halt
  simpa [hPre] using Program.withSubroutine_getElem?_suffix pre (compile source) [.halt]
    (87 + (compile source).length + 1) 0

/-- The entry phase is executed from ordinary raw machine input. Its cost
includes every write, copy, clear, rewind, and return jump. -/
theorem initializedCompile_prepare_eval (source : Program) (input : List Bool) :
    evalConfigWithin (initializedCompile source) (Configuration.initial input)
      (31 * input.length + 42) =
      PMF.pure ((encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87) := by
  have h := prepareTapes_withSubroutine_eval []
    ((compile source).asSubroutine 87 (87 + (compile source).length + 1) ++ [.halt])
    87 [] [] input
  have hInitial : packInputStart [] [] input = Configuration.initial input := by cases input <;> rfl
  rw [hInitial] at h
  change evalConfigWithin (initializedCompile source) (Configuration.initial input)
    (31 * input.length + 42) = PMF.pure ((prepareTapesFinish [] [] input).resumeAt 87) at h
  have hEntry : (prepareTapesFinish [] [] input).resumeAt 87 =
      (encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87 := by
    simp [prepareTapesFinish, Configuration.resumeAt, Configuration.rebasePc,
      encodeConfiguration, address, preparedSource]
  exact h.trans (congrArg PMF.pure hEntry)

/-- Every branch of the initialized source call returns by the simulation
budget, and the following halt consumes one additional native transition. -/
theorem initializedCompile_call_halts (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    ∀ final, PaddedRunsFor (initializedCompile source)
      ((encodeConfiguration source.length (input.reverse.map some) []
        (preparedSource input)).rebasePc 87)
      final (preparedTraceBudget q input.length + 1) → final.halted = true := by
  let pre := prepareTapes.asSubroutine 0 87
  let entry := encodeConfiguration source.length (input.reverse.map some) [] (preparedSource input)
  let returnPc := 87 + (compile source).length + 1
  have hPre : pre.length = 87 := rfl
  have hPc : entry.pc ≤ (compile source).length := by
    simp [entry, encodeConfiguration, preparedSource, address]
  have hActive : entry.halted = false := rfl
  have hReturns : ReturnsWithin (initializedCompile source) (entry.rebasePc 87)
      returnPc (preparedTraceBudget q input.length) := by
    intro final run
    by_contra hNoReturn
    change ReturnRunsFor (Program.withSubroutine pre (compile source) [.halt] returnPc)
      returnPc (entry.rebasePc pre.length) final (preparedTraceBudget q input.length) at run
    obtain ⟨d, hRun, hdActive, _, _⟩ := run.source_of_not_returned
      pre (compile source) [.halt] returnPc hPc hActive hNoReturn
    have hdHalted := compile_prepared_all_branches_halted source input q halts
      (input.reverse.map some) [] d hRun.toPadded
    simp [hdActive] at hdHalted
  have hInstr : (initializedCompile source)[returnPc]? = some .halt := by
    exact initializedCompile_halt_instruction source
  exact hReturns.all_branches_halted_after_halt hInstr

theorem initializedCompile_haltsWithin (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    HaltsWithin (initializedCompile source) input
      (31 * input.length + 42 + preparedTraceBudget q input.length + 1) := by
  intro final run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [show 31 * input.length + 42 + preparedTraceBudget q input.length + 1 =
      (31 * input.length + 42) + (preparedTraceBudget q input.length + 1) by omega,
    evalConfigWithin_add, initializedCompile_prepare_eval, PMF.pure_bind] at hMem
  exact initializedCompile_call_halts source input q halts final
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)

/-- Source polynomial time gives all-branch polynomial time of this
operationally initialized guarded execution. Output is still encoded, so
this theorem alone does not establish an adversary-interface simulation. -/
theorem initializedCompile_polynomialTime (source : Program) (h : PolynomialTime source) :
    PolynomialTime (initializedCompile source) := by
  obtain ⟨q, hq, halts⟩ := h
  refine ⟨fun m => 31 * m + 42 + preparedTraceBudget q m + 1, ?_, ?_⟩
  · exact ((((PolynomiallyBounded.const 31).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 42)).add (preparedTraceBudget_polynomiallyBounded hq)).add
      (PolynomiallyBounded.const 1)
  · intro input
    exact initializedCompile_haltsWithin source input q (halts input)

/-- Probability correctness of the actual initialized program on raw
inputs. Its output is still the physical guarded encoding of the source
output tape. This is an equality of distributions across all random paths,
not a free output-decoding operation or an adversary-interface theorem. -/
theorem initializedCompile_output_eval (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    (evalConfigWithin (initializedCompile source) (Configuration.initial input)
      (31 * input.length + 42 + preparedTraceBudget q input.length + 1)).map
        Configuration.outputBits =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (encodeConfiguration source.length (input.reverse.map some) [] c).outputBits) := by
  let pre := prepareTapes.asSubroutine 0 87
  let entry := encodeConfiguration source.length (input.reverse.map some) [] (preparedSource input)
  let returnPc := 87 + (compile source).length + 1
  have hPre : pre.length = 87 := rfl
  have hPc : entry.pc ≤ (compile source).length := by
    simp [entry, encodeConfiguration, preparedSource, address]
  have hActive : entry.halted = false := rfl
  have hLayout : ∀ pc, pc ≤ (compile source).length → pre.length + pc ≠ returnPc := by
    intro pc hpc
    rw [hPre]
    dsimp [returnPc]
    omega
  have hCompile := compile_eval_of_all_branches_halted source (q input.length) (preparedSource input)
    (preparedSource_all_branches_halted source input _ halts)
    (preparedTraceBudget q input.length + 1)
    (by
      have hStorage := preparedSource_sourceStorage_le input
      have hBound : q input.length * (17 * (sourceStorage (preparedSource input) + q input.length) + 23) ≤
          preparedTraceBudget q input.length := by
        apply Nat.mul_le_mul_left
        omega
      exact hBound.trans (Nat.le_succ (preparedTraceBudget q input.length)))
    (input.reverse.map some) []
  rw [show 31 * input.length + 42 + preparedTraceBudget q input.length + 1 =
      (31 * input.length + 42) + (preparedTraceBudget q input.length + 1) by omega,
    evalConfigWithin_add, initializedCompile_prepare_eval, PMF.pure_bind]
  change (evalConfigWithin (Program.withSubroutine pre (compile source) [.halt] returnPc)
    (entry.rebasePc pre.length) (preparedTraceBudget q input.length + 1)).map
      Configuration.outputBits = _
  have hInstr : (Program.withSubroutine pre (compile source) [.halt] returnPc)[returnPc]? = some .halt := by
    change (initializedCompile source)[returnPc]? = some .halt
    exact initializedCompile_halt_instruction source
  rw [Program.evalConfigWithin_output_eq_evalReturnWithin_of_halt
    (Program.withSubroutine pre (compile source) [.halt] returnPc) returnPc hInstr,
    Program.evalReturnWithin_output_eq pre (compile source) [.halt] returnPc hLayout
      entry hPc hActive]
  rw [hCompile, PMF.map_comp]
  rfl

end Machine.GuardedCompiler
