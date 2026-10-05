import Foundation.Crypto.Semantics.Machine.GuardedTape

namespace Machine.GuardedCompiler

/-- Represented storage of both logical source tapes. This quantity is
used only to bound the actual work of the compiled boundary-growth routine. -/
def sourceStorage (c : Configuration) : Nat := c.inputTape.cells + c.outputTape.cells

private theorem storage_le_of_instruction (i : Instruction) (c d : Configuration)
    (h : d ∈ match some (i.next c) with
      | none => []
      | some (.inl target) => [target]
      | some (.inr (left, right)) => [left, right]) :
    sourceStorage d ≤ sourceStorage c + 1 := by
  cases i with
  | halt =>
      simp [Instruction.next] at h
      subst d
      simp [sourceStorage]
  | moveLeft which =>
      simp [Instruction.next] at h
      subst d
      cases which with
      | input =>
          have hMove := Tape.cells_moveLeft_le c.inputTape
          simp only [sourceStorage, Configuration.advance, Configuration.updateTape]
          omega
      | output =>
          have hMove := Tape.cells_moveLeft_le c.outputTape
          simp only [sourceStorage, Configuration.advance, Configuration.updateTape]
          omega
  | moveRight which =>
      simp [Instruction.next] at h
      subst d
      cases which with
      | input =>
          have hMove := Tape.cells_moveRight_le c.inputTape
          simp only [sourceStorage, Configuration.advance, Configuration.updateTape]
          omega
      | output =>
          have hMove := Tape.cells_moveRight_le c.outputTape
          simp only [sourceStorage, Configuration.advance, Configuration.updateTape]
          omega
  | write which bit =>
      simp [Instruction.next] at h
      subst d
      cases which <;> simp [sourceStorage, Configuration.advance,
        Configuration.updateTape, Tape.cells_write]
  | erase which =>
      simp [Instruction.next] at h
      subst d
      cases which <;> simp [sourceStorage, Configuration.advance,
        Configuration.updateTape, Tape.cells_write]
  | branch which blankPc zeroPc onePc =>
      simp [Instruction.next] at h
      subst d
      simp [sourceStorage]
  | jump pc =>
      simp [Instruction.next] at h
      subst d
      simp [sourceStorage]
  | randomBit which =>
      simp [Instruction.next] at h
      rcases h with h | h <;> subst d <;>
        cases which <;> simp [sourceStorage, Configuration.advance,
          Configuration.updateTape, Tape.cells_write]

theorem sourceStorage_le_of_step {source : Program} {c d : Configuration}
    (step : Step source c d) : sourceStorage d ≤ sourceStorage c + 1 := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  cases hRead : source[c.pc]? with
  | none =>
      have hd : d = { c with halted := true } := by
        simpa [Step, successors, next, hActive, hRead] using step
      subst d
      simp [sourceStorage]
  | some i =>
      apply storage_le_of_instruction i c d
      cases hNext : i.next c <;>
        simpa [Step, successors, next, hActive, hRead, hNext] using step

theorem sourceStorage_le_of_run {source : Program} {start finish : Configuration}
    {steps : Nat} (run : RunsFor source start finish steps) :
    sourceStorage finish ≤ sourceStorage start + steps := by
  induction run with
  | zero => simp
  | succ prior last ih =>
      have hStep := sourceStorage_le_of_step last
      omega

/-- Bookkeeping padding after halt does not increase either tape's storage.
The bound still charges every possible actual transition, including both
outcomes of a random-bit instruction. -/
theorem sourceStorage_le_of_padded_run {source : Program} {start finish : Configuration}
    {steps : Nat} (run : PaddedRunsFor source start finish steps) :
    sourceStorage finish ≤ sourceStorage start + steps := by
  induction run with
  | zero => simp
  | succ prior last ih =>
      rcases last with hStep | ⟨_, rfl⟩
      · have hNext := sourceStorage_le_of_step hStep
        omega
      · omega

/-- Any finite source trace has a matching actual compiled trace on the
same represented tapes and saved prefixes. The work bound is polynomial
in source transition count and initial source storage:
`steps * (17 * (sourceStorage start + steps) + 23)`.
This direction alone does not prove universal compiled termination: it
does not yet classify every target trace, initialize raw input, extract
output, or equate the whole-program probability distributions. -/
theorem compile_runs {source : Program} {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ steps * (17 * (sourceStorage start + steps) + 23) ∧
      RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput start)
        (encodeConfiguration source.length beforeInput beforeOutput finish) used := by
  induction run with
  | zero => exact ⟨0, by simp, RunsFor.zero _⟩
  | @succ middle finish steps prior last ih =>
      obtain ⟨used, hUsed, compiledPrior⟩ := ih
      obtain ⟨tail, hTail, compiledLast⟩ := compile_step_runs source middle finish last
        beforeInput beforeOutput
      have hStorage := sourceStorage_le_of_run prior
      have hLast : tail ≤ 17 * (sourceStorage start + steps) + 23 := by
        change tail ≤ 17 * sourceStorage middle + 23 at hTail
        omega
      refine ⟨used + tail, ?_, compiledPrior.trans compiledLast⟩
      calc
        used + tail ≤ steps * (17 * (sourceStorage start + steps) + 23) +
            (17 * (sourceStorage start + steps) + 23) := Nat.add_le_add hUsed hLast
        _ = (steps + 1) * (17 * (sourceStorage start + steps) + 23) := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ (steps + 1) * (17 * (sourceStorage start + (steps + 1)) + 23) :=
          Nat.mul_le_mul_left _ (by omega)

/-- Scalar upper bound for a forward simulation of a source execution
using at most `q m` transitions on a raw source input of length `m`.
Input preparation and output extraction are additional obligations. -/
def traceBudget (q : Nat → Nat) (m : Nat) : Nat :=
  q m * (17 * (m + 2 + q m) + 23)

theorem traceBudget_polynomiallyBounded {q : Nat → Nat} (h : PolynomiallyBounded q) :
    PolynomiallyBounded (traceBudget q) :=
  h.mul (((PolynomiallyBounded.const 17).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)).add h)).add
      (PolynomiallyBounded.const 23))

theorem initial_sourceStorage_le (input : List Bool) :
    sourceStorage (Configuration.initial input) ≤ input.length + 2 := by
  cases input with
  | nil => simp [sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells]
  | cons bit rest =>
      simp [sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells]
      omega

/-- Every source execution within its input-length budget has a matching
compiled execution within the displayed polynomial majorant. The start
state is explicitly the encoded source state; it is not a raw machine
initial state. This statement makes no converse trace or all-target-branch
termination claim. -/
theorem compile_runs_initial {source : Program} {input : List Bool}
    {finish : Configuration} {steps : Nat} (q : Nat → Nat)
    (run : RunsFor source (Configuration.initial input) finish steps)
    (hSteps : steps ≤ q input.length) (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ traceBudget q input.length ∧
      RunsFor (compile source)
        (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
        (encodeConfiguration source.length beforeInput beforeOutput finish) used := by
  obtain ⟨used, hUsed, compiled⟩ := compile_runs run beforeInput beforeOutput
  have hStorage := initial_sourceStorage_le input
  refine ⟨used, hUsed.trans ?_, compiled⟩
  exact Nat.mul_le_mul hSteps (by omega)

end Machine.GuardedCompiler
