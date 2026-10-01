import Foundation.Constructions.ElGamal.MachineSimulatorSemantics

namespace ElGamal.Examples.MachineSimulator

open Machine

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
  {M : RepresentedMachinePrimitives sampling X embed}
  (N : RepresentedChooseNormalizer M)

/-- The finite compiler handles encoded source code without consulting the
current family, parameter, instance, or machine probability distribution. -/
example (source : Program) :
    N.simulatorCompiler.runCode (Program.encode source) =
      some (Program.encode (N.simulatorCode source)) := by
  rw [ProgramCompiler.runCode_encode, N.simulatorCompiler_run]

example (source : Program) :
    (N.simulatorCompiler.run source).length =
      136 * source.length + 68 * N.program.length + 68 * M.multiplyProgram.length + 1764 := by
  rw [N.simulatorCompiler_run, N.simulatorCode_length]

/-- The common majorant covers all represented instances, challenge tuples,
and source choose branches. It bounds charged native machine transitions. -/
example (source : Program) (q : Nat → Nat) (hPolynomial : PolynomiallyBounded q) :
    ∃ budget : Nat → Nat, PolynomiallyBounded budget ∧
      ∀ n (x : X n) (first second last : (embed n x).params.Element),
        N.simulatorBudget source q n x first second last ≤ budget n :=
  N.simulatorBudget_uniform_polynomial source q hPolynomial

/-- The actual compiler realizes the existing Phase 11 adversary family
with a polynomial evaluation budget. All-bitstring stopping, required by
machine PPT membership, is a separate remaining obligation. -/
example (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (A : AdversaryFamily (representedINDCPAGoal sampling X embed) F)
    (source : Program) (q : Nat → Nat) (hPolynomial : PolynomiallyBounded q)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (hRealize : (representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode).Realizes
      F source q A) :
    ∃ targetBudget : Nat → Nat, PolynomiallyBounded targetBudget ∧
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).Realizes
        ((representedReduction sampling X embed).mapFamily F) (N.simulatorCode source) targetBudget
        ((representedReduction sampling X embed).mapAdversaryFamily F A) :=
  N.nativeSimulator_polynomial_realization F A source q hPolynomial hSource hRealize

/-- The useful reachable-request source class supplies exactly the source
code, polynomial stopping profile and realization premise consumed above.
This example asserts target realization, not target PPT membership. -/
example (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (A : AdversaryFamily (representedINDCPAGoal sampling X embed) F)
    (hA : (representedINDCPAElementPPTClass sampling X embed M.instanceCode M.elementCode).admissible F A) :
    ∃ (source : Program) (targetBudget : Nat → Nat), PolynomiallyBounded targetBudget ∧
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).Realizes
        ((representedReduction sampling X embed).mapFamily F) (N.simulatorCode source) targetBudget
        ((representedReduction sampling X embed).mapAdversaryFamily F A) := by
  obtain ⟨source, q, _size, hPolynomial, hSource, _hSize, _hChoose, _hGuess, hRealize⟩ := hA
  obtain ⟨targetBudget, hTargetPolynomial, hTargetRealize⟩ :=
    N.nativeSimulator_polynomial_realization F A source q hPolynomial hSource hRealize
  exact ⟨source, targetBudget, hTargetPolynomial, hTargetRealize⟩

end ElGamal.Examples.MachineSimulator
