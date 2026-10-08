import Foundation.Crypto.Semantics.Machine.Execution

/-! A finite decidable sufficient condition for native control to remain
inside its source block until halt. This checks instruction addresses only;
termination, running time and cryptographic correctness remain separate. -/
namespace Machine

/-- Every active successor of this instruction lies inside the given code. -/
def Instruction.ControlClosedAt (size pc : Nat) : Instruction → Prop
  | .halt => True
  | .branch _ blank zero one => blank < size ∧ zero < size ∧ one < size
  | .jump target => target < size
  | _ => pc + 1 < size

instance (size pc : Nat) (instruction : Instruction) : Decidable (instruction.ControlClosedAt size pc) := by
  cases instruction <;> simp only [Instruction.ControlClosedAt] <;> infer_instance

/-- A finite syntactic check; no quantification over machine tapes occurs. -/
def Program.ControlClosed (code : Program) : Prop :=
  ∀ pc : Fin code.length, (code[pc.val]).ControlClosedAt code.length pc.val

instance (code : Program) : Decidable code.ControlClosed := by
  unfold Program.ControlClosed
  infer_instance

/-- The finite check implies the operational closure premise needed by
probabilistic subroutine composition, including both random successors. -/
theorem Program.controlClosed_step {code : Program} (hClosed : code.ControlClosed)
    (start target : Configuration) (hp : start.pc < code.length)
    (hs : Step code start target) (ha : target.halted = false) : target.pc < code.length := by
  have hActive : start.halted = false := by
    cases h : start.halted with
    | false => rfl
    | true => exact False.elim (no_step_of_halted h hs)
  have updatePc (which : TapeId) (f : Tape → Tape) : (start.updateTape which f).pc = start.pc := by
    cases which <;> rfl
  have hc := hClosed ⟨start.pc, hp⟩
  have lookup : code[start.pc]? = some code[start.pc] := List.getElem?_eq_getElem hp
  simp only [Step, successors, next, hActive, Bool.false_eq_true, ↓reduceIte, lookup] at hs
  generalize hi : code[start.pc] = instruction at hs hc
  cases instruction <;>
    simp only [Instruction.next, Instruction.ControlClosedAt, List.mem_cons, List.not_mem_nil, or_false] at hs hc
  · subst target; simp at ha
  · subst target; simpa [Configuration.advance, updatePc] using hc
  · subst target; simpa [Configuration.advance, updatePc] using hc
  · subst target; simpa [Configuration.advance, updatePc] using hc
  · subst target; simpa [Configuration.advance, updatePc] using hc
  · subst target
    cases h : (start.tape _).current with
    | none => simpa [h] using hc.1
    | some bit => cases bit <;> simp [h, hc.2.1, hc.2.2]
  · subst target; simpa [Configuration.advance, updatePc] using hc
  · rcases hs with rfl | rfl <;> simpa [Configuration.advance, updatePc] using hc

end Machine
