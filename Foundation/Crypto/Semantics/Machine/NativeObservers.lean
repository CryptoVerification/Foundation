import Foundation.Crypto.Semantics.Machine.NativeContinuation

/-! Two fixed finite observers on the actual inherited output tape. Neither
observer reconstructs a list or resets tape heads. The first reads the current
cell (blank is false); the second uses a genuine fresh random-bit instruction. -/
namespace Machine.NativeObservers
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def firstCode : Program :=
  [.branch .output 1 1 3, .write .output false, .halt, .write .output true, .halt]

def firstValue (machine : Configuration) : Bool := machine.outputTape.current.getD false

def firstExit (machine : Configuration) : Configuration :=
  {machine.resumeAt 0 with
    pc := if firstValue machine then 4 else 2
    outputTape := machine.outputTape.write (some (firstValue machine))
    halted := true}

theorem first_run (machine : Configuration) :
    evalConfigWithin firstCode (machine.resumeAt 0) 3 = PMF.pure (firstExit machine) := by
  rcases h : machine.outputTape.current with _ | b
  · simp [evalConfigWithin, firstCode, stepPMF, next, Instruction.next,
      Configuration.resumeAt, Configuration.advance, Configuration.tape, Configuration.updateTape, Tape.write, firstExit, firstValue, h]
  · cases b <;> simp [evalConfigWithin, firstCode, stepPMF, next, Instruction.next,
      Configuration.resumeAt, Configuration.advance, Configuration.tape, Configuration.updateTape, Tape.write, firstExit, firstValue, h]

noncomputable def first : Machine.Procedure Configuration Configuration :=
  Machine.Procedure.ofFixed firstCode (fun machine => machine.resumeAt 0)
    (fun _ output => output) (fun machine => PMF.pure (firstExit machine)) (fun _ => 3)
    (fun machine => by simpa only [PMF.pure_map] using first_run machine)

theorem first_halted (input output : Configuration)
    (h : output ∈ (first.execution.semantics input).support) : output.halted = true := by
  change output ∈ (PMF.pure (firstExit input)).support at h
  rw [PMF.mem_support_pure_iff] at h
  subst output
  rfl

def randomCode : Program := [.randomBit .output, .halt]

def randomExit (machine : Configuration) (bit : Bool) : Configuration :=
  {machine.resumeAt 0 with pc := 1, outputTape := machine.outputTape.write (some bit), halted := true}

theorem random_run (machine : Configuration) :
    evalConfigWithin randomCode (machine.resumeAt 0) 2 = sampleBit.map (randomExit machine) := by
  simp only [evalConfigWithin, PMF.pure_bind, stepPMF, next, Configuration.resumeAt,
    Bool.false_eq_true, ↓reduceIte, randomCode, List.getElem?_cons_zero, Instruction.next,
    PMF.bind_map, Function.comp_def]
  congr 1
  funext bit
  cases bit <;> rfl

noncomputable def random : Machine.Procedure Configuration Configuration :=
  Machine.Procedure.ofFixed randomCode (fun machine => machine.resumeAt 0)
    (fun _ output => output) (fun machine => sampleBit.map (randomExit machine)) (fun _ => 2)
    (fun machine => by simpa only [PMF.map_comp, Function.comp_def] using random_run machine)

theorem random_halted (input output : Configuration)
    (h : output ∈ (random.execution.semantics input).support) : output.halted = true := by
  change output ∈ (sampleBit.map (randomExit input)).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨bit, _, rfl⟩ := h
  rfl

end Machine.NativeObservers
