import Foundation.Crypto.Semantics.Machine.ConfigurationEncoding
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Account for program counters and finite code as well as represented
tape cells. Jump addresses are charged even when they lie outside the code.
The actual finite code is constant across security parameters. Unary coding
is conservative; no cost for producing the representation is asserted. -/
namespace Machine
open Foundation.Probability

def Instruction.addressCap : Instruction → Nat
  | .branch _ blankPc zeroPc onePc => max blankPc (max zeroPc onePc)
  | .jump pc => pc
  | _ => 0

def Program.addressCap : Program → Nat
  | [] => 0
  | i :: rest => i.addressCap + Program.addressCap rest

theorem addressCap_le_of_mem (code : Program) (i : Instruction) (h : i ∈ code) :
    i.addressCap ≤ code.addressCap := by
  induction code with
  | nil => simp at h
  | cons head rest ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp [Program.addressCap]
      · have ht := ih h
        simp only [Program.addressCap]
        omega

theorem pc_le_of_instruction (i : Instruction) (c d : Configuration)
    (h : d ∈ match some (i.next c) with
      | none => []
      | some (.inl target) => [target]
      | some (.inr (left, right)) => [left, right]) :
    d.pc ≤ c.pc + i.addressCap + 1 := by
  cases i with
  | branch tape blankPc zeroPc onePc =>
      simp [Instruction.next] at h
      subst d
      cases hc : (c.tape tape).current with
      | none => simp [Instruction.addressCap]; omega
      | some b => cases b <;> simp [Instruction.addressCap] <;> omega
  | randomBit tape =>
      simp [Instruction.next] at h
      rcases h with h | h <;> subst d <;> cases tape <;>
        simp [Configuration.advance, Configuration.updateTape, Instruction.addressCap]
  | halt => simp [Instruction.next] at h; subst d; simp [Instruction.addressCap]
  | jump pc => simp [Instruction.next] at h; subst d; simp [Instruction.addressCap]; omega
  | moveLeft tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape, Instruction.addressCap]
  | moveRight tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape, Instruction.addressCap]
  | write tape bit =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape, Instruction.addressCap]
  | erase tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape, Instruction.addressCap]

theorem pc_le_of_step {code : Program} {c d : Configuration}
    (h : Step code c d) : d.pc ≤ c.pc + (code.addressCap + 1) := by
  by_cases hh : c.halted = true
  · exact False.elim (no_step_of_halted hh h)
  · have hf : c.halted = false := by cases hflag : c.halted <;> simp_all
    cases hi : code[c.pc]? with
    | none =>
        have hd : d = { c with halted := true } := by
          simpa [Step, successors, next, hf, hi] using h
        subst d
        simp
    | some i =>
        have hMem := addressCap_le_of_mem code i (List.mem_of_getElem? hi)
        have hd := pc_le_of_instruction i c d (by
          cases hn : i.next c <;> simpa [Step, successors, next, hf, hi, hn] using h)
        omega

theorem pc_le_of_support (code : Program) (c d : Configuration)
    (h : d ∈ (stepPMF code c).support) : d.pc ≤ c.pc + (code.addressCap + 1) := by
  rcases (mem_support_stepPMF_iff code c d).mp h with hStep | ⟨_, rfl⟩
  · exact pc_le_of_step hStep
  · omega

theorem pc_prefix (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF code) elapsed start).support) :
    target.pc ≤ start.pc + horizon * (code.addressCap + 1) :=
  TimedExecution.ResourceGrowth.prefix_bound (stepPMF code) Configuration.pc
    (code.addressCap + 1) (pc_le_of_support code) horizon elapsed hElapsed start target h

/-- Bit length of a faithful full configuration representation, with the
actual encoded finite program retained once. -/
def Configuration.codeAndStateBits (code : Program) (c : Configuration) : Nat :=
  (Program.encode code).length + (ConfigurationEncoding.configuration.encode c).length

def Program.storageBound (code : Program) (initialPc initialCells horizon : Nat) : Nat :=
  (Program.encode code).length + 2 * (initialPc + horizon * (code.addressCap + 1)) +
    18 * (initialCells + horizon) + 14

theorem codeAndStateBits_prefix (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF code) elapsed start).support) :
    target.codeAndStateBits code ≤ code.storageBound start.pc start.tapeCells horizon := by
  have hp := pc_prefix code horizon elapsed hElapsed start target h
  have ht := tapeCells_prefix code horizon elapsed hElapsed start target h
  have he := ConfigurationEncoding.configuration_length_le target
  unfold Configuration.codeAndStateBits Program.storageBound
  omega

theorem storageBound_polynomial (code : Program) {initialPc initialCells horizon : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hCells : PolynomiallyBounded initialCells)
    (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => code.storageBound (initialPc n) (initialCells n) (horizon n)) := by
  exact (((PolynomiallyBounded.const (Program.encode code).length).add
    ((PolynomiallyBounded.const 2).mul (hPc.add (hTime.mul (PolynomiallyBounded.const (code.addressCap + 1)))))).add
      ((PolynomiallyBounded.const 18).mul (hCells.add hTime))).add (PolynomiallyBounded.const 14)

theorem Procedure.codeAndStateBits_prefix {Input Output : Type*} (P : Procedure Input Output)
    (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ P.execution.budget input)
    (target : Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF P.code) elapsed (P.execution.entry input)).support) :
    target.codeAndStateBits P.code ≤ P.code.storageBound (P.execution.entry input).pc
      (P.execution.entry input).tapeCells (P.execution.budget input) :=
  Machine.codeAndStateBits_prefix P.code _ elapsed hElapsed _ target h

theorem Procedure.codeAndStateBits_exit {Input Output : Type*} (P : Procedure Input Output)
    (input : Input)
    (hHalt : ∀ output ∈ (P.execution.semantics input).support,
      (P.execution.exit input output).halted = true)
    (output : Output) (hOutput : output ∈ (P.execution.semantics input).support) :
    (P.execution.exit input output).codeAndStateBits P.code ≤
      P.code.storageBound (P.execution.entry input).pc (P.execution.entry input).tapeCells
        (P.execution.budget input) := by
  have hs : P.execution.exit input output ∈
      (TimedExecution.eval (stepPMF P.code) (P.execution.budget input) (P.execution.entry input)).support := by
    rw [timed_eval_eq, P.final_run input hHalt _ (Nat.le_refl _), PMF.mem_support_map_iff]
    exact ⟨output, hOutput, rfl⟩
  exact P.codeAndStateBits_prefix input _ (Nat.le_refl _) _ hs

end Machine
