import Foundation.Crypto.Semantics.Machine.ProgramRanking

/-! A ranked native program with branch-dependent actual stopping times.
The same fixed code takes three transitions on false and four on true;
its ranked certificate retains that joint law instead of padding both to four. -/
namespace Foundation.Examples.RankedVariableTime
open Machine Foundation.Probability TimedExecution

def code : Machine.Program := [.randomBit .output, .branch .output 2 2 3, .halt, .jump 2]

def assertions : Machine.Program.Assertions where
  active pc _ _ := pc ≤ 3
  stopped _ _ _ := True

theorem verified : assertions.Verified code := by
  constructor
  · intro pc start hPc hActive hAssertion
    fin_cases pc
    all_goals
      cases hc : start.outputTape.current with
      | none => simp_all [code, assertions, Program.Assertions.Holds, Instruction.precondition,
          Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]
      | some bit => cases bit <;>
          simp_all [code, assertions, Program.Assertions.Holds, Instruction.precondition,
            Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]
  · intro _ _ _ _ _
    trivial

def rank (state : Configuration) : Nat :=
  match state.pc with
  | 0 => 3
  | 1 => 2
  | 3 => 1
  | _ => 0

def ranking : Program.Ranking assertions code where
  rank := rank
  instruction := by
    intro pc start hPc hActive hAssertion
    fin_cases pc
    all_goals
      cases hc : start.outputTape.current with
      | none => simp_all [code, rank, assertions, Program.Assertions.Holds, Instruction.precondition,
          Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]
      | some bit => cases bit <;>
          simp_all [code, rank, assertions, Program.Assertions.Holds, Instruction.precondition,
            Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape]

def initial (input : Tape) : Configuration := {inputTape := input}

def finish (input : Tape) (bit : Bool) : Configuration :=
  {pc := 2, inputTape := input, outputTape := ({ } : Tape).write (some bit), halted := true}

theorem initial_valid (input : Tape) : assertions.Holds (initial input) := by
  simp [assertions, Program.Assertions.Holds, initial]

noncomputable def native := ranking.onInputs verified initial initial_valid

theorem budget (input : Tape) : native.execution.budget input = 4 := rfl

/-- The actual first-arrival law distinguishes the two durations. -/
theorem boundary_law (input : Tape) :
    runToBoundary (stepPMF code) Configuration.halted 4 (initial input) =
      sampleBit.map (fun bit => (finish input bit, if bit then 4 else 3)) := by
  rw [runToBoundary]
  change (stepPMF code (initial input)).bind (fun middle =>
    (runToBoundary (stepPMF code) Configuration.halted 3 middle).map
      (fun result => (result.1, result.2 + 1))) = _
  simp only [stepPMF, Machine.next, initial, code, List.getElem?_cons_zero, Bool.false_eq_true,
    ↓reduceIte, Instruction.next, Configuration.updateTape, Configuration.advance]
  rw [PMF.bind_map]
  change sampleBit.bind _ = sampleBit.bind (fun bit => PMF.pure (finish input bit, if bit then 4 else 3))
  congr 1
  funext bit
  cases bit <;> simp [runToBoundary, stepPMF, Machine.next, Instruction.next,
    Configuration.tape, Configuration.advance, Configuration.updateTape, Tape.write, finish,
    PMF.pure_map, PMF.pure_bind]

theorem costed (input : Tape) :
    (native.execution.costed input).map (fun result => (result.1.val, result.2)) =
      sampleBit.map (fun bit => (finish input bit, if bit then 4 else 3)) := by
  have h := ranking.costed verified initial initial_valid input
  change _ = runToBoundary (stepPMF code) Configuration.halted 4 (initial input) at h
  exact h.trans (boundary_law input)

end Foundation.Examples.RankedVariableTime
