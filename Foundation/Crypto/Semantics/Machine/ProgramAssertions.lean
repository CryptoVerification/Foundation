import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.Invariant

/-! Local assertions for finite probabilistic bit code. Verification checks
one obligation per instruction address and a separate implicit-falloff rule.
Both random successors must satisfy the next assertion. These are partial
correctness rules: no termination or cryptographic assumption is required. -/
namespace Machine
open Foundation.Probability TimedExecution

/-- A weakest precondition for one actual instruction, including both coins. -/
def Instruction.precondition (instruction : Instruction) (post : Configuration → Prop)
    (start : Configuration) : Prop :=
  match instruction.next start with
  | .inl target => post target
  | .inr (zero, one) => post zero ∧ post one

@[simp] theorem Instruction.precondition_halt (post : Configuration → Prop) (start : Configuration) :
    Instruction.halt.precondition post start = post {start with halted := true} := rfl

@[simp] theorem Instruction.precondition_randomBit (which : TapeId)
    (post : Configuration → Prop) (start : Configuration) :
    (Instruction.randomBit which).precondition post start =
      (post ((start.updateTape which (fun tape => tape.write (some false))).advance) ∧
       post ((start.updateTape which (fun tape => tape.write (some true))).advance)) := rfl

/-- The local obligation covers every operational successor. -/
theorem Instruction.precondition_step {code : Program} {instruction : Instruction}
    {start target : Configuration} {property : Configuration → Prop} (hLookup : code[start.pc]? = some instruction)
    (hActive : start.halted = false) (hStep : Step code start target)
    (hPre : instruction.precondition (fun target => property target) start) : property target := by
  cases hNext : instruction.next start with
  | inl result =>
      have he : target = result := by
        simpa [Step, successors, Machine.next, hActive, hLookup, hNext] using hStep
      simpa only [Instruction.precondition, hNext, he] using hPre
  | inr pair =>
      rcases pair with ⟨zero, one⟩
      have he : target = zero ∨ target = one := by
        simpa [Step, successors, Machine.next, hActive, hLookup, hNext] using hStep
      simp only [Instruction.precondition, hNext] at hPre
      rcases he with rfl | rfl
      · exact hPre.1
      · exact hPre.2

/-- The one-instruction precondition is exact, not merely sufficient. -/
theorem Instruction.precondition_iff {code : Program} {instruction : Instruction}
    {start : Configuration} {property : Configuration → Prop}
    (hLookup : code[start.pc]? = some instruction) (hActive : start.halted = false) :
    instruction.precondition property start ↔
      ∀ target, Step code start target → property target := by
  constructor
  · intro hPre target hStep
    exact Instruction.precondition_step hLookup hActive hStep hPre
  · intro hAll
    cases hNext : instruction.next start with
    | inl result =>
        simp only [Instruction.precondition, hNext]
        exact hAll result (by simp [Step, successors, Machine.next, hActive, hLookup, hNext])
    | inr pair =>
        rcases pair with ⟨zero, one⟩
        simp only [Instruction.precondition, hNext]
        constructor
        · exact hAll zero (by simp [Step, successors, Machine.next, hActive, hLookup, hNext])
        · exact hAll one (by simp [Step, successors, Machine.next, hActive, hLookup, hNext])

structure Program.Assertions where
  active : Nat → Tape → Tape → Prop
  stopped : Nat → Tape → Tape → Prop

namespace Program.Assertions

def Holds (assertions : Program.Assertions) (machine : Configuration) : Prop :=
  if machine.halted then assertions.stopped machine.pc machine.inputTape machine.outputTape
  else assertions.active machine.pc machine.inputTape machine.outputTape

/-- Finite-address instruction obligations, plus the machine's implicit halt
outside the instruction list. A jump out of range is never silently accepted. -/
structure Verified (assertions : Program.Assertions) (code : Program) : Prop where
  instruction : ∀ pc : Fin code.length, ∀ start : Configuration,
    start.pc = pc.val → start.halted = false →
    assertions.active pc.val start.inputTape start.outputTape →
      (code[pc.val]).precondition assertions.Holds start
  outside : ∀ pc input output, code.length ≤ pc →
    assertions.active pc input output → assertions.stopped pc input output

variable {assertions : Program.Assertions} {code : Program}

theorem Verified.preserves (verified : assertions.Verified code) :
    Preserves (stepPMF code) assertions.Holds := by
  intro start hStart target hTarget
  rcases (mem_support_stepPMF_iff code start target).mp hTarget with hs | ⟨_, rfl⟩
  · have ha : start.halted = false := by
      cases hh : start.halted with
      | false => rfl
      | true => exact False.elim (no_step_of_halted hh hs)
    have hActive : assertions.active start.pc start.inputTape start.outputTape := by
      simpa only [Holds, ha, Bool.false_eq_true, ↓reduceIte] using hStart
    by_cases hp : start.pc < code.length
    · exact Instruction.precondition_step (List.getElem?_eq_getElem hp) ha hs
        (verified.instruction ⟨start.pc, hp⟩ start rfl ha hActive)
    · have hLookup : code[start.pc]? = none := List.getElem?_eq_none (by omega)
      have he : target = {start with halted := true} := by
        simpa [Step, successors, next, ha, hLookup] using hs
      rw [he]
      exact verified.outside start.pc start.inputTape start.outputTape (by omega) hActive
  · exact hStart

/-- Completeness relative to the supplied assertions: one-step preservation
is equivalent to the finite instruction obligations and falloff obligation. -/
theorem Verified.of_preserves (hPreserves : Preserves (stepPMF code) assertions.Holds) :
    assertions.Verified code := by
  constructor
  · intro pc start hPc hActive hAssertion
    have hLookup : code[start.pc]? = some code[pc.val] := by
      rw [hPc]
      exact List.getElem?_eq_getElem pc.isLt
    apply (Instruction.precondition_iff hLookup hActive).mpr
    intro target hStep
    apply hPreserves start _ target ((mem_support_stepPMF_iff code start target).mpr (Or.inl hStep))
    simpa only [Holds, hActive, Bool.false_eq_true, ↓reduceIte, hPc] using hAssertion
  · intro pc input output hOutside hAssertion
    let start : Configuration := {pc := pc, inputTape := input, outputTape := output}
    have hLookup : code[start.pc]? = none := List.getElem?_eq_none hOutside
    have hStep : Step code start {start with halted := true} := by
      simp [Step, successors, next, start, hLookup]
    have h := hPreserves start (by exact hAssertion) {start with halted := true}
      ((mem_support_stepPMF_iff code _ _).mpr (Or.inl hStep))
    exact h

theorem verified_iff_preserves : assertions.Verified code ↔
    Preserves (stepPMF code) assertions.Holds :=
  ⟨Verified.preserves, Verified.of_preserves⟩

/-- Independent assertion proofs can be combined without redoing the
instruction-level analysis. The combination keeps both full-tape conditions. -/
def inter (first second : Program.Assertions) : Program.Assertions where
  active pc input output := first.active pc input output ∧ second.active pc input output
  stopped pc input output := first.stopped pc input output ∧ second.stopped pc input output

theorem holds_inter (first second : Program.Assertions) (machine : Configuration) :
    (first.inter second).Holds machine ↔ first.Holds machine ∧ second.Holds machine := by
  cases hh : machine.halted <;> simp [Holds, inter, hh]

theorem Verified.inter {first second : Program.Assertions}
    (hFirst : first.Verified code) (hSecond : second.Verified code) :
    (first.inter second).Verified code := by
  apply Verified.of_preserves
  intro start hStart target hTarget
  rw [holds_inter] at hStart ⊢
  exact ⟨hFirst.preserves start hStart.1 target hTarget,
    hSecond.preserves start hStart.2 target hTarget⟩

/-- Every prefix, at arbitrary fuel, satisfies the address-indexed assertion. -/
theorem Verified.prefix (verified : assertions.Verified code) (start target : Configuration)
    (hStart : assertions.Holds start) (elapsed : Nat)
    (hTarget : target ∈ (evalConfigWithin code start elapsed).support) : assertions.Holds target := by
  rw [← timed_eval_eq] at hTarget
  exact eval_preserves _ _ verified.preserves elapsed start target hStart hTarget

/-- Successful stopping implies the postcondition; stopping itself is not a conclusion. -/
theorem Verified.partial_correctness (verified : assertions.Verified code)
    (start target : Configuration) (hStart : assertions.Holds start) (elapsed : Nat)
    (hTarget : target ∈ (evalConfigWithin code start elapsed).support)
    (hHalted : target.halted = true) : assertions.stopped target.pc target.inputTape target.outputTape := by
  have h := verified.prefix start target hStart elapsed hTarget
  simpa only [Holds, hHalted, ↓reduceIte] using h

/-- Actual first-arrival endpoints and fuel-exhausted endpoints both obey the
invariant. This assertion does not confuse exhaustion with boundary success. -/
theorem Verified.boundary (verified : assertions.Verified code) (boundary : Configuration → Bool)
    (fuel : Nat) (start : Configuration) (result : Configuration × Nat)
    (hStart : assertions.Holds start)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support) :
    assertions.Holds result.1 :=
  boundary_preserves _ _ verified.preserves boundary fuel start result hStart hResult

end Program.Assertions
end Machine
