import Foundation.Crypto.Semantics.Machine.SubroutineProbability

namespace Machine

/-- Exchange the two finite tape selectors in code. This is a syntax
operation performed when constructing a wrapper, not a runtime instruction. -/
def TapeId.swap : TapeId → TapeId
  | .input => .output
  | .output => .input

/-- Relabel only tape operands. Every original branch address and bit is
retained; the instruction still performs the same one-cell operation. -/
def Instruction.swapTapes : Instruction → Instruction
  | .halt => .halt
  | .moveLeft tape => .moveLeft tape.swap
  | .moveRight tape => .moveRight tape.swap
  | .write tape bit => .write tape.swap bit
  | .erase tape => .erase tape.swap
  | .branch tape blankPc zeroPc onePc => .branch tape.swap blankPc zeroPc onePc
  | .jump pc => .jump pc
  | .randomBit tape => .randomBit tape.swap

def Program.swapTapes (p : Program) : Program := p.map Instruction.swapTapes

/-- A relation between the layouts of two executions. No machine executes a
whole-tape swap in one transition: the paired run uses relabeled instructions
on the opposite physical tapes. -/
def Configuration.swapTapes (c : Configuration) : Configuration :=
  { c with inputTape := c.outputTape, outputTape := c.inputTape }

@[simp] theorem TapeId.swap_swap (tape : TapeId) : tape.swap.swap = tape := by cases tape <;> rfl
@[simp] theorem Instruction.swapTapes_swapTapes (i : Instruction) : i.swapTapes.swapTapes = i := by
  cases i <;> simp [Instruction.swapTapes]
@[simp] theorem Program.swapTapes_length (p : Program) : p.swapTapes.length = p.length := by
  simp [Program.swapTapes]
@[simp] theorem Program.swapTapes_swapTapes (p : Program) : p.swapTapes.swapTapes = p := by
  simp [Program.swapTapes, List.map_map, Function.comp_def]
@[simp] theorem Configuration.swapTapes_swapTapes (c : Configuration) : c.swapTapes.swapTapes = c := rfl

private def swapSuccessor : Configuration ⊕ (Configuration × Configuration) →
    Configuration ⊕ (Configuration × Configuration)
  | .inl c => .inl c.swapTapes
  | .inr (c, d) => .inr (c.swapTapes, d.swapTapes)

theorem Instruction.next_swapTapes (i : Instruction) (c : Configuration) :
    i.swapTapes.next c.swapTapes = swapSuccessor (i.next c) := by
  cases i with
  | halt => rfl
  | jump pc => rfl
  | moveLeft tape => cases tape <;> rfl
  | moveRight tape => cases tape <;> rfl
  | write tape bit => cases tape <;> rfl
  | erase tape => cases tape <;> rfl
  | randomBit tape => cases tape <;> rfl
  | branch tape blankPc zeroPc onePc => cases tape <;> rfl

theorem next_swapTapes (p : Program) (c : Configuration) :
    next p.swapTapes c.swapTapes = (next p c).map swapSuccessor := by
  cases hHalted : c.halted with
  | true => simp [next, Configuration.swapTapes, hHalted]
  | false =>
      simp only [next, Configuration.swapTapes, hHalted, Bool.false_eq_true, ↓reduceIte,
        Program.swapTapes, List.getElem?_map, Option.map_some]
      cases hInstruction : p[c.pc]? with
      | none => rfl
      | some i => simpa only [Option.map_some, Configuration.swapTapes, hHalted] using congrArg some (Instruction.next_swapTapes i c)

theorem successors_swapTapes (p : Program) (c : Configuration) :
    successors p.swapTapes c.swapTapes = (successors p c).map Configuration.swapTapes := by
  simp only [successors, next_swapTapes]
  cases next p c with
  | none => rfl
  | some result => cases result <;> rfl

/-- Each possible branch, including either outcome of a random instruction,
has a corresponding relabeled branch with exactly one native transition. -/
theorem Step.swapTapes {p : Program} {c d : Configuration} (step : Step p c d) :
    Step p.swapTapes c.swapTapes d.swapTapes := by
  rw [Step, successors_swapTapes, List.mem_map]
  exact ⟨d, step, rfl⟩

theorem RunsFor.swapTapes {p : Program} {c d : Configuration} {steps : Nat}
    (run : RunsFor p c d steps) : RunsFor p.swapTapes c.swapTapes d.swapTapes steps := by
  induction run with
  | zero => exact RunsFor.zero _
  | succ prior last ih => exact RunsFor.succ ih last.swapTapes

/-- Both successors retain their original fair-bit probabilities. Tape
relabeling neither supplies external randomness nor drops any random branch. -/
theorem stepPMF_swapTapes (p : Program) (c : Configuration) :
    stepPMF p.swapTapes c.swapTapes = (stepPMF p c).map Configuration.swapTapes := by
  simp only [stepPMF, next_swapTapes]
  cases hNext : next p c with
  | none => simp [PMF.pure_map]
  | some result =>
      cases result with
      | inl d => simp [swapSuccessor, PMF.pure_map]
      | inr pair =>
          rcases pair with ⟨d₀, d₁⟩
          simp only [Option.map_some, swapSuccessor, PMF.map_comp]
          congr 1
          funext bit
          cases bit <;> rfl

/-- Complete finite-fuel configuration semantics. The two executions take
the same transition budget and preserve the entire distribution of both
physical tapes, heads, control, and halt status. -/
theorem evalConfigWithin_swapTapes (p : Program) (c : Configuration) (steps : Nat) :
    evalConfigWithin p.swapTapes c.swapTapes steps =
      (evalConfigWithin p c steps).map Configuration.swapTapes := by
  induction steps generalizing c with
  | zero => simp [evalConfigWithin, PMF.pure_map]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, stepPMF_swapTapes, PMF.bind_map,
        evalConfigWithin_succ_head, PMF.map_bind]
      simp only [Function.comp_def, ih]

/-- Relabeling also commutes with source-call address relocation. This
allows native input-reading routines to operate on the physical output tape
while caller-owned data remain on the physical input tape. -/
theorem Program.swapTapes_asSubroutine (p : Program) (base returnPc : Nat) :
    (p.asSubroutine base returnPc).swapTapes = p.swapTapes.asSubroutine base returnPc := by
  simp only [Program.swapTapes, Program.asSubroutine, List.map_append, List.map_map,
    List.map_cons, List.map_nil, List.length_map]
  congr 1
  apply congrArg (fun f => p.map f)
  funext i
  cases i <;> rfl

/-- Tape-operand relabeling preserves native control closure. Branch and
return addresses are unchanged; this theorem does not add a machine step. -/
theorem Program.controlClosed_swapTapes (p : Program)
    (closed : ∀ c d, c.pc < p.length → Step p c d → d.halted = false → d.pc < p.length)
    (c d : Configuration) (hPc : c.pc < p.swapTapes.length)
    (step : Step p.swapTapes c d) (hRunning : d.halted = false) :
    d.pc < p.swapTapes.length := by
  have original := step.swapTapes
  simp only [Program.swapTapes_swapTapes] at original
  simpa only [Configuration.swapTapes, Program.swapTapes_length] using
    closed c.swapTapes d.swapTapes (by simpa [Configuration.swapTapes] using hPc) original hRunning

end Machine
