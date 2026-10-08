import Foundation.Crypto.Semantics.Machine.RankedFamily
import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.Machine.ControlClosure
import Foundation.Crypto.Semantics.Machine.NativeComponent

/-! Append one fixed bit to an arbitrary inherited output packet. Three
actual native instructions write, move the head and halt. The packet and
saved input tape are input-dependent proof parameters, never free runtime
copies. Local assertions and a rank construct the execution contract. -/
namespace Machine.OutputAppend
open Foundation.Probability TimedExecution

def code (bit : Bool) : Program := [.write .output bit, .moveRight .output, .halt]

def written (packet : List Bool) (bit : Bool) : Tape :=
  (ResponseExport.endTape packet).write (some bit)

theorem written_moveRight (packet : List Bool) (bit : Bool) :
    (written packet bit).moveRight = ResponseExport.endTape (packet ++ [bit]) := by
  simp [written, ResponseExport.endTape, Tape.write, Tape.moveRight]

def assertions (packet : List Bool) (saved : Tape) (bit : Bool) : Program.Assertions where
  active pc input output := input = saved ∧
    ((pc = 0 ∧ output = ResponseExport.endTape packet) ∨
     (pc = 1 ∧ output = written packet bit) ∨
     (pc = 2 ∧ output = ResponseExport.endTape (packet ++ [bit])))
  stopped _ input output := input = saved ∧ output = ResponseExport.endTape (packet ++ [bit])

theorem verified (packet : List Bool) (saved : Tape) (bit : Bool) :
    (assertions packet saved bit).Verified (code bit) := by
  constructor
  · intro pc start hPc hActive hAssertion
    fin_cases pc <;>
      simp_all [code, assertions, Program.Assertions.Holds, Instruction.precondition,
        Instruction.next, Configuration.updateTape, Configuration.advance, written]
    all_goals exact written_moveRight packet bit
  · intro pc input output hOutside hAssertion
    obtain ⟨_, hPc⟩ := hAssertion
    change 3 ≤ pc at hOutside
    rcases hPc with ⟨hPc, _⟩ | ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> omega

def ranking (packet : List Bool) (saved : Tape) (bit : Bool) :
    Program.Ranking (assertions packet saved bit) (code bit) where
  rank := fun machine => 2 - machine.pc
  instruction := by
    intro pc start hPc hActive _
    fin_cases pc <;>
      simp_all [code, Instruction.precondition, Instruction.next,
        Configuration.updateTape, Configuration.advance]

def initial (packet : List Bool) (saved : Tape) : Configuration :=
  {inputTape := saved, outputTape := ResponseExport.endTape packet}

theorem initial_valid (packet : List Bool) (saved : Tape) (bit : Bool) :
    (assertions packet saved bit).Holds (initial packet saved) := by
  simp [initial, assertions, Program.Assertions.Holds]

noncomputable def family (bit : Bool) : Program.RankedFamily (code bit) (List Bool × Tape) where
  assertions := fun input => assertions input.1 input.2 bit
  verified := fun input => verified input.1 input.2 bit
  ranking := fun input => ranking input.1 input.2 bit
  entry := fun input => initial input.1 input.2
  valid := fun input => initial_valid input.1 input.2 bit

noncomputable def native (bit : Bool) : Machine.Procedure (List Bool × Tape) Configuration :=
  (family bit).native

theorem budget (packet : List Bool) (saved : Tape) (bit : Bool) :
    (native bit).execution.budget (packet, saved) = 3 := rfl

theorem output (packet : List Bool) (saved : Tape) (bit : Bool) (machine : Configuration)
    (h : machine ∈ ((native bit).execution.semantics (packet, saved)).support) :
    machine.inputTape = saved ∧ machine.outputTape = ResponseExport.endTape (packet ++ [bit]) :=
  (family bit).stopped (packet, saved) machine h

theorem closed (bit : Bool) (start target : Configuration) (hPc : start.pc < (code bit).length)
    (hStep : Step (code bit) start target) (hActive : target.halted = false) :
    target.pc < (code bit).length := by
  apply Program.controlClosed_step _ start target hPc hStep hActive
  intro pc
  fin_cases pc <;> simp [code, Instruction.ControlClosedAt]

noncomputable def component (bit : Bool) : NativeComponent (List Bool × Tape) Configuration :=
  NativeComponent.ofRankedFamily (family bit) (closed bit)
    (fun _ => by change 0 < 3; decide) (fun _ => rfl)

def finish (packet : List Bool) (saved : Tape) (bit : Bool) : Configuration :=
  {pc := 2, inputTape := saved, outputTape := ResponseExport.endTape (packet ++ [bit]), halted := true}

theorem run (packet : List Bool) (saved : Tape) (bit : Bool) :
    evalConfigWithin (code bit) (initial packet saved) 3 = PMF.pure (finish packet saved bit) := by
  simp [evalConfigWithin, stepPMF, Machine.next, code, initial, Instruction.next,
    Configuration.updateTape, Configuration.advance, finish,
    ResponseExport.endTape, Tape.write, Tape.moveRight, PMF.pure_bind]

theorem semantics (packet : List Bool) (saved : Tape) (bit : Bool) :
    (native bit).execution.semantics (packet, saved) = PMF.pure (finish packet saved bit) := by
  change (family bit).execution.semantics (packet, saved) = _
  rw [← (family bit).run (packet, saved) 3 (Nat.le_refl 3)]
  exact run packet saved bit

end Machine.OutputAppend
