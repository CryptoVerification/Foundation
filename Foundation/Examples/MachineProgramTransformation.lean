import Foundation.Machine.ProgramTransformation
import Foundation.Examples.MachinePPT

namespace Machine.Examples

/-- A toy reduction with zero advantage. Its target adversary always answers
`false`, independently of the source adversary. -/
noncomputable def constantAnswerReduction : Reduction bitGoal bitGoal where
  mapInstance := fun I => I
  reduce := fun _ _ => fun _ => PMF.pure false
  loss := AdvantageBound.id
  advantage_le := by intro n I A; simp [bitGoal]

/-- This finite compiler syntax emits one halt instruction. Its interpreter
is structurally recursive and inspects no instance family. -/
def constantAnswerCompiler : Machine.ProgramCompiler :=
  .constant haltImmediately

def constantAnswerTransformation :
    constantAnswerReduction.MachineProgramTransformation bitInterface bitInterface where
  compiler := constantAnswerCompiler
  transformBudget := fun _ _ => 1
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  budget_bound := by intro q m; simp
  halts := by
    intro p q _ input
    exact haltImmediately_haltsWithin input
  realizes := by
    intro F A p q _
    unfold MachineAdversaryInterface.Realizes
    funext n
    funext request
    change bitInterface.responseWithin haltImmediately (fun _ => 1) n (F n) request =
      PMF.pure false
    simp [MachineAdversaryInterface.responseWithin, MachineAdversaryInterface.machineInput,
      evalWithin, evalConfigWithin, stepPMF, next, Instruction.next,
      haltImmediately, Configuration.initial, Configuration.outputBits,
      Tape.bits, PMF.pure_bind, PMF.pure_map,
      bitInterface, FiniteBitEncoding.bool]
  mapInputSize := by intro F size; exact size
  size_polynomial := by intro F size h; exact h

example : constantAnswerCompiler.run randomOutputBit = haltImmediately := rfl

example : constantAnswerCompiler.runCode (Machine.Program.encode randomOutputBit) =
    some (Machine.Program.encode haltImmediately) := by
  simp [constantAnswerCompiler, Machine.ProgramCompiler.run]

/-- A second finite compiler genuinely uses the source code. The appended
halt changes the syntax but not a single machine transition, so both the
operational runtime and the realized adversary family are preserved. -/
def appendHaltTransformation :
    (Reduction.id bitGoal).MachineProgramTransformation bitInterface bitInterface where
  compiler := .suffix [.halt]
  transformBudget := fun q => q
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  budget_bound := by intro q m; simp
  halts := by
    intro p q h input
    exact (haltsWithin_append_halt_iff p input (q input.length)).2 (h input)
  realizes := by
    intro F A p q h
    unfold MachineAdversaryInterface.Realizes at h ⊢
    change bitInterface.realizeFamily F (p ++ [.halt]) q = A
    rw [bitInterface.realizeFamily_append_halt]
    exact h
  mapInputSize := by intro F size; exact size
  size_polynomial := by intro F size h; exact h

example : appendHaltTransformation.transform randomOutputBit =
    randomOutputBit ++ [.halt] := rfl

example :
    appendHaltTransformation.compiler.runCode
      (Machine.Program.encode randomOutputBit) =
        some (Machine.Program.encode (randomOutputBit ++ [.halt])) := by
  simp [appendHaltTransformation, Machine.ProgramCompiler.run]

example : (Reduction.id bitGoal).PreservesAdmissibility
    bitInterface.pptClass bitInterface.pptClass :=
  appendHaltTransformation.preservesAdmissibility

example : (constantAnswerTransformation.comp
    (Reduction.MachineProgramTransformation.id bitInterface)).transform
      randomOutputBit = haltImmediately := rfl

example : constantAnswerReduction.PreservesAdmissibility
    bitInterface.pptClass bitInterface.pptClass :=
  constantAnswerTransformation.preservesAdmissibility

noncomputable example : constantAnswerReduction.MachineProgramSimulation
    bitInterface bitInterface :=
  constantAnswerTransformation.toSimulation

example :
    (constantAnswerTransformation.toSimulation.comp
      (Reduction.MachineProgramSimulation.id bitInterface)).transform
        randomOutputBit = haltImmediately := rfl

example :
    (constantAnswerReduction.comp (Reduction.id bitGoal)).PreservesAdmissibility
      bitInterface.pptClass bitInterface.pptClass :=
  (constantAnswerTransformation.comp
    (Reduction.MachineProgramTransformation.id bitInterface)).preservesAdmissibility

end Machine.Examples
