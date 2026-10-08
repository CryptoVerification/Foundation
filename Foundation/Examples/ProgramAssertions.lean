import Foundation.Crypto.Semantics.Machine.SubroutineAssertions
import Foundation.Crypto.Semantics.Machine.ControlClosure

/-! An invariant for a nonterminating random native loop, with arbitrary
inherited tapes. At its jump address the output head must contain a bit.
No coin branch, source width, or prefix length is singled out. -/
namespace Foundation.Examples.ProgramAssertions
open Machine Foundation.Probability

def code : Machine.Program := [.randomBit .output, .jump 0]

def assertions (saved : Tape) : Machine.Program.Assertions where
  active pc input output := input = saved ∧
    (pc = 0 ∨ pc = 1 ∧ output.current.isSome = true)
  stopped _ _ _ := False

theorem verified (saved : Tape) : (assertions saved).Verified code := by
  constructor
  · intro pc start hPc hActive hAssertion
    fin_cases pc <;>
      simp_all [code, assertions, Program.Assertions.Holds, Instruction.precondition,
        Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write]
  · intro pc input output hOutside hAssertion
    obtain ⟨_, hPc⟩ := hAssertion
    change 2 ≤ pc at hOutside
    rcases hPc with hPc | ⟨hPc, _⟩ <;> omega

def initial (saved output : Tape) : Configuration :=
  {inputTape := saved, outputTape := output}

theorem initial_valid (saved output : Tape) : (assertions saved).Holds (initial saved output) := by
  simp [Program.Assertions.Holds, assertions, initial]

/-- Every finite prefix retains the complete input tape and its head. -/
theorem input_preserved (saved output : Tape) (elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalConfigWithin code (initial saved output) elapsed).support) :
    target.inputTape = saved := by
  have h := (verified saved).prefix _ _ (initial_valid saved output) elapsed hTarget
  cases hh : target.halted with
  | false => exact (show (assertions saved).active target.pc target.inputTape target.outputTape from
      (by simpa only [Program.Assertions.Holds, hh, Bool.false_eq_true, ↓reduceIte] using h)).1
  | true => simp [Program.Assertions.Holds, hh, assertions] at h

/-- Partial correctness proves a genuine invariant without claiming a halt. -/
theorem never_halts (saved output : Tape) (elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalConfigWithin code (initial saved output) elapsed).support) :
    target.halted = false := by
  cases hh : target.halted with
  | false => rfl
  | true => exact False.elim ((verified saved).partial_correctness _ _
      (initial_valid saved output) elapsed hTarget hh)

/-- The callee's arbitrary native embedding keeps the inherited input tape,
without assuming termination or charging a halt that never happens. -/
theorem embedded_input (saved output : Tape) (pre suffix : Machine.Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < code.length → pre.length + pc ≠ returnPc)
    (elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalReturnWithin (Program.withSubroutine pre code suffix returnPc)
      returnPc ((initial saved output).rebasePc pre.length) elapsed).support) :
    target.inputTape = saved := by
  apply (verified saved).subroutine_tapes pre suffix returnPc hLayout
    (Program.controlClosed_step (by decide)) (fun input _ => input = saved) _
    (initial saved output) (by change 0 < 2; decide) rfl (initial_valid saved output) elapsed target hTarget
  intro sourceState h
  cases hh : sourceState.halted with
  | false => exact (show (assertions saved).active sourceState.pc sourceState.inputTape sourceState.outputTape from
      (by simpa only [Program.Assertions.Holds, hh, Bool.false_eq_true, ↓reduceIte] using h)).1
  | true => simp [Program.Assertions.Holds, hh, assertions] at h

/-- Checking only listed instructions would accept this bad specification:
the jump exits the list and the required stopping condition is false. -/
def badCode : Machine.Program := [.jump 1]

def badAssertions : Machine.Program.Assertions where
  active pc _ _ := pc ≤ 1
  stopped _ _ _ := False

theorem bad_instruction_obligations : ∀ pc : Fin badCode.length, ∀ start : Configuration,
    start.pc = pc.val → start.halted = false →
    badAssertions.active pc.val start.inputTape start.outputTape →
      (badCode[pc.val]).precondition badAssertions.Holds start := by
  intro pc start hPc hActive hAssertion
  fin_cases pc
  simp [badCode, badAssertions, Program.Assertions.Holds, Instruction.precondition,
    Instruction.next, hActive]

theorem bad_rejected : ¬ badAssertions.Verified badCode := by
  intro h
  exact h.outside 1 {} {} (by decide) (by change 1 ≤ 1; omega)

end Foundation.Examples.ProgramAssertions
