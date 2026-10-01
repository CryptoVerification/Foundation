import Foundation.Constructions.ElGamal.MachinePrimitives
import Foundation.Constructions.ElGamal.MachineRepresented
import Foundation.Machine.SubroutineProbability

namespace ElGamal.Examples

variable
  {sampling : (n : Nat) → (params : DDHParameters) →
    Option (DDHFiniteSampling params)}
  {X : Nat → Type 1}
  {embed : ∀ n, X n → ConcreteInstance sampling n}
  (M : RepresentedMachinePrimitives sampling X embed)

/-- Specializing to different families changes only represented inputs and
proofs. All three operation codes remain identical. -/
example (F G : (n : Nat) → X n) :
    ((M.forFamily F).multiplyProgram, (M.forFamily F).powerProgram,
      (M.forFamily F).sampleProgram) =
    ((M.forFamily G).multiplyProgram, (M.forFamily G).powerProgram,
      (M.forFamily G).sampleProgram) := rfl

example : Machine.PolynomialTime M.multiplyProgram ∧
    Machine.PolynomialTime M.powerProgram ∧
    Machine.PolynomialTime M.sampleProgram :=
  ⟨⟨M.multiplyBudget, M.multiplyBudget_polynomial, M.multiplyHalts⟩,
    ⟨M.powerBudget, M.powerBudget_polynomial, M.powerHalts⟩,
    ⟨M.sampleBudget, M.sampleBudget_polynomial, M.sampleHalts⟩⟩

/-- A multiplication invocation retains the standalone all-branch step
bound when its caller supplies the matching initial tapes. -/
example (pre suffix : Machine.Program) (returnPc : Nat) (input : List Bool) :
    Machine.ReturnsWithin
      (Machine.Program.withSubroutine pre M.multiplyProgram suffix returnPc)
      ((Machine.Configuration.initial input).rebasePc pre.length)
      returnPc (M.multiplyBudget input.length) :=
  (M.multiplyHalts input).withSubroutine_returnsWithin
    pre M.multiplyProgram suffix returnPc

/-- The sampler's universal stopping certificate covers every random branch
of an invocation. It supplies no free or unit-cost sampling primitive. -/
example (pre suffix : Machine.Program) (returnPc : Nat) (input : List Bool) :
    Machine.ReturnsWithin
      (Machine.Program.withSubroutine pre M.sampleProgram suffix returnPc)
      ((Machine.Configuration.initial input).rebasePc pre.length)
      returnPc (M.sampleBudget input.length) :=
  (M.sampleHalts input).withSubroutine_returnsWithin
    pre M.sampleProgram suffix returnPc

/-- The current-instance and element length certificates also discharge the
target DDH adapter's complete input-size obligation. This statement does not
construct the two-stage IND-CPA simulator or its tape preparation. -/
example (F : InstanceFamily (representedINDCPAGoal sampling X embed)) :
    ∃ size :
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).InputSizeBound
        ((representedReduction sampling X embed).mapFamily F),
      PolynomiallyBounded size.limit := by
  exact Machine.ddhReindexedTripleInputSizeBound
    (concreteDDHSemantics sampling) X (fun n x => (embed n x).params)
    M.instanceCode M.elementCode M.instanceCodeLength M.elementCodeLength
    M.instanceCode_length_le M.elementCode_length_le
    M.instanceCodeLength_polynomial M.elementCodeLength_polynomial
    ((representedReduction sampling X embed).mapFamily F)

/-- The represented multiplication certificate remains correct when its
code is invoked as a subroutine. The invocation is entered with fresh tapes;
this proves no surrounding protocol's tape preparation or state isolation. -/
example (pre suffix : Machine.Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ M.multiplyProgram.length → pre.length + pc ≠ returnPc)
    (n : Nat) (x : X n) (a b : (embed n x).params.Element) :
    let input := Machine.encodeSecurityParameter n ++
      Machine.frame ((M.instanceCode n).encode x) ++
      Machine.frame ((M.elementCode n x).encode a) ++
      Machine.frame ((M.elementCode n x).encode b)
    (Machine.evalReturnWithin
      (Machine.Program.withSubroutine pre M.multiplyProgram suffix returnPc)
      returnPc ((Machine.Configuration.initial input).rebasePc pre.length)
      (M.multiplyBudget input.length)).map
        (fun c => if c.pc = returnPc then some c.outputBits else none) =
      PMF.pure (some ((M.elementCode n x).encode ((embed n x).params.mul a b))) := by
  dsimp only
  exact ((M.multiplyHalts _).withSubroutine_evalReturn
    pre M.multiplyProgram suffix returnPc hLayout).trans (M.multiply_correct n x a b)

/-- An explicit sampler certificate gives the same decoded scalar PMF in an
embedded invocation. Exact sampling and worst-case termination are supplied
by the certificate; neither follows just from a finite algebraic domain. -/
example (pre suffix : Machine.Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ M.sampleProgram.length → pre.length + pc ≠ returnPc)
    (n : Nat) (x : X n) :
    let input := Machine.encodeSecurityParameter n ++
      Machine.frame ((M.instanceCode n).encode x)
    ((Machine.evalReturnWithin
      (Machine.Program.withSubroutine pre M.sampleProgram suffix returnPc)
      returnPc ((Machine.Configuration.initial input).rebasePc pre.length)
      (M.sampleBudget input.length)).map
        (fun c => if c.pc = returnPc then some c.outputBits else none)).map
          (fun bits => bits.bind (M.scalarCode n x).decode) =
      ((embed n x).algebra.sampling.sampleScalar).map some := by
  dsimp only
  rw [(M.sampleHalts _).withSubroutine_evalReturn
    pre M.sampleProgram suffix returnPc hLayout]
  exact M.sample_correct n x

end ElGamal.Examples
