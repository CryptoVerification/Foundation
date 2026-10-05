import Foundation.Crypto.Semantics.Machine.ProgramTransformation
import Foundation.Crypto.Semantics.Machine.Security
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
    intro F A p q _hHalts _hRealizes
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
    intro F A p q _hHalts h
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

/-- This syntax-changing certificate prepares tapes, simulates all source
random branches, and extracts raw output using actual machine instructions. -/
example : (Reduction.MachineProgramTransformation.guarded bitInterface).transform randomOutputBit =
    GuardedCompiler.rawCompile randomOutputBit := rfl

example : (Reduction.MachineProgramTransformation.guarded bitInterface).coefficient = 125 := rfl
example : (Reduction.MachineProgramTransformation.guarded bitInterface).securityDegree = 1 := rfl
example : (Reduction.MachineProgramTransformation.guarded bitInterface).sourceDegree = 2 := rfl

example : (Reduction.id bitGoal).PreservesAdmissibility bitInterface.pptClass bitInterface.pptClass :=
  (Reduction.MachineProgramTransformation.guarded bitInterface).preservesAdmissibility

example : PolynomialTime (GuardedCompiler.rawCompile randomOutputBit) :=
  (Reduction.MachineProgramTransformation.guarded bitInterface).preservesPolynomialTime
    randomOutputBit_polynomialTime

/-- The explicit finite compiler certificate composes in the existing
reduction order. Neither call initializes or decodes tapes for free. -/
example : ((Reduction.MachineProgramTransformation.guarded bitInterface).comp
    (Reduction.MachineProgramTransformation.guarded bitInterface)).transform randomOutputBit =
      GuardedCompiler.rawCompile (GuardedCompiler.rawCompile randomOutputBit) := rfl

example : ((Reduction.MachineProgramTransformation.guarded bitInterface).comp
    (Reduction.MachineProgramTransformation.guarded bitInterface)).coefficient = 125 * (125 + 1)^2 := rfl

example : ((Reduction.MachineProgramTransformation.guarded bitInterface).comp
    (Reduction.MachineProgramTransformation.guarded bitInterface)).securityDegree = 3 := rfl

example : ((Reduction.MachineProgramTransformation.guarded bitInterface).comp
    (Reduction.MachineProgramTransformation.guarded bitInterface)).sourceDegree = 4 := rfl

example (F : InstanceFamily bitGoal)
    (hSecure : SecureOnWithin bitGoal bitInterface.pptClass F) :
    SecureOnWithin bitGoal bitInterface.pptClass F :=
  (Reduction.id bitGoal).secureOnWithin_machinePPT bitInterface bitInterface F
    (Reduction.MachineProgramTransformation.guarded bitInterface)
    AdvantageBound.id_preservesNegligible hSecure

/-- Polynomiality alone does not bound a source budget at an expanded input
by fixed metadata applied to its value at the original input. A finite spike
already disproves that inference. A protocol compiler must establish its
`budget_bound` from the actual source invocations, rather than infer it only
from `PolynomiallyBounded`. This is a scalar sanity check, not a claim that a
particular machine or ElGamal compiler is impossible. -/
example (c k d : Nat) :
    ∃ q : Nat → Nat, PolynomiallyBounded q ∧
      ¬ q 2 ≤ c * (1 + 1)^k * (q 1 + 1)^d := by
  let spike := c * 2^k + 1
  let q : Nat → Nat := fun m => if m = 2 then spike else 0
  refine ⟨q, ?_, ?_⟩
  · apply PolynomiallyBounded.mono (s := fun _ => spike)
    · intro m
      dsimp [q]
      split <;> omega
    · exact PolynomiallyBounded.const spike
  · simp [q, spike]

end Machine.Examples
