import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ResourceGrowth

/-! Storage measured in represented cells of both physical tape zippers.
This counts blanks and retained cells on both sides of each head. Finite
program code, control integers, and enclosing oracle states are separate
resources; this measure makes no claim about their memory representation. -/
namespace Machine
open Foundation.Probability

def Configuration.tapeCells (c : Configuration) : Nat :=
  c.inputTape.cells + c.outputTape.cells

theorem Tape.cells_ofBits_le (bits : List Bool) :
    (Tape.ofBits bits).cells ≤ bits.length + 1 := by
  cases bits with
  | nil => simp [Tape.ofBits, Tape.cells]
  | cons bit rest => simp [Tape.ofBits, Tape.cells]; omega

theorem tapeCells_le_of_instruction (i : Instruction) (c d : Configuration)
    (h : d ∈ match some (i.next c) with
      | none => []
      | some (.inl target) => [target]
      | some (.inr (left, right)) => [left, right]) :
    d.tapeCells ≤ c.tapeCells + 1 := by
  cases i with
  | moveLeft tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;>
        simp only [Configuration.tapeCells, Configuration.advance, Configuration.updateTape]
      · have hb := Tape.cells_moveLeft_le c.inputTape
        omega
      · have hb := Tape.cells_moveLeft_le c.outputTape
        omega
  | moveRight tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;>
        simp only [Configuration.tapeCells, Configuration.advance, Configuration.updateTape]
      · have hb := Tape.cells_moveRight_le c.inputTape
        omega
      · have hb := Tape.cells_moveRight_le c.outputTape
        omega
  | randomBit tape =>
      simp [Instruction.next] at h
      rcases h with h | h <;> subst d <;> cases tape <;>
        simp [Configuration.tapeCells, Configuration.advance, Configuration.updateTape,
          Tape.cells_write]
  | write tape bit =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.tapeCells, Configuration.advance,
        Configuration.updateTape, Tape.cells_write]
  | erase tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.tapeCells, Configuration.advance,
        Configuration.updateTape, Tape.cells_write]
  | halt => simp [Instruction.next] at h; subst d; simp [Configuration.tapeCells]
  | branch tape a b e => simp [Instruction.next] at h; subst d; simp [Configuration.tapeCells]
  | jump pc => simp [Instruction.next] at h; subst d; simp [Configuration.tapeCells]

theorem tapeCells_le_of_step {code : Program} {c d : Configuration}
    (h : Step code c d) : d.tapeCells ≤ c.tapeCells + 1 := by
  by_cases hh : c.halted = true
  · exact False.elim (no_step_of_halted hh h)
  · have hf : c.halted = false := by cases hflag : c.halted <;> simp_all
    cases hi : code[c.pc]? with
    | none =>
        have hd : d = { c with halted := true } := by
          simpa [Step, successors, next, hf, hi] using h
        subst d
        simp [Configuration.tapeCells]
    | some i =>
        apply tapeCells_le_of_instruction i c d
        cases hn : i.next c <;> simpa [Step, successors, next, hf, hi, hn] using h

theorem tapeCells_le_of_support (code : Program) (c d : Configuration)
    (h : d ∈ (stepPMF code c).support) : d.tapeCells ≤ c.tapeCells + 1 := by
  rcases (mem_support_stepPMF_iff code c d).mp h with hStep | ⟨_, rfl⟩
  · exact tapeCells_le_of_step hStep
  · omega

/-- The peak over every possible prefix, including random branches. -/
theorem tapeCells_prefix (code : Program) (horizon elapsed : Nat)
    (hElapsed : elapsed ≤ horizon) (start intermediate : Configuration)
    (h : intermediate ∈ (TimedExecution.eval (stepPMF code) elapsed start).support) :
    intermediate.tapeCells ≤ start.tapeCells + horizon := by
  simpa using TimedExecution.ResourceGrowth.prefix_bound (stepPMF code)
    Configuration.tapeCells 1 (tapeCells_le_of_support code)
    horizon elapsed hElapsed start intermediate h

theorem tapeCells_boundary (code : Program) (boundary : Configuration → Bool)
    (fuel : Nat) (start : Configuration) (result : Configuration × Nat)
    (h : result ∈ (TimedExecution.runToBoundary (stepPMF code) boundary fuel start).support) :
    result.1.tapeCells ≤ start.tapeCells + result.2 := by
  simpa using TimedExecution.ResourceGrowth.boundary_endpoint (stepPMF code)
    Configuration.tapeCells 1 (tapeCells_le_of_support code) boundary fuel start result h

/-- Any existing native procedure inherits the peak bound without a new
scheme-specific execution proof. -/
theorem Procedure.tapeCells_prefix {Input Output : Type*} (P : Procedure Input Output)
    (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ P.execution.budget input)
    (intermediate : Configuration)
    (h : intermediate ∈ (TimedExecution.eval (stepPMF P.code) elapsed
      (P.execution.entry input)).support) :
    intermediate.tapeCells ≤ (P.execution.entry input).tapeCells + P.execution.budget input :=
  Machine.tapeCells_prefix P.code _ elapsed hElapsed _ intermediate h

/-- Logical outputs inherit the bound when their physical exits are halted.
The halt hypothesis lets the procedure's residual law identify actual exits. -/
theorem Procedure.tapeCells_exit {Input Output : Type*} (P : Procedure Input Output)
    (input : Input)
    (hHalt : ∀ output ∈ (P.execution.semantics input).support,
      (P.execution.exit input output).halted = true)
    (output : Output) (hOutput : output ∈ (P.execution.semantics input).support) :
    (P.execution.exit input output).tapeCells ≤
      (P.execution.entry input).tapeCells + P.execution.budget input := by
  have hSupport : P.execution.exit input output ∈
      (TimedExecution.eval (stepPMF P.code) (P.execution.budget input)
        (P.execution.entry input)).support := by
    rw [timed_eval_eq, P.final_run input hHalt _ (Nat.le_refl _), PMF.mem_support_map_iff]
    exact ⟨output, hOutput, rfl⟩
  exact P.tapeCells_prefix input _ (Nat.le_refl _) _ hSupport

end Machine
