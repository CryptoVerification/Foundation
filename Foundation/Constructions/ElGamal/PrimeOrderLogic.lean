import Foundation.Constructions.ElGamal.PrimeOrderMachineSecurity
import Foundation.Constructions.ElGamal.Logic

namespace ElGamal.PrimeOrderRepresentation

/-- The concrete executable compiler contains only the two fixed operation codes. -/
def logicCompiler : Machine.ProgramCompiler :=
  .comp (.chooseChallenge Machine.ChooseSafeValidation.program
    Machine.FramedProductSafeMultiply.program) .identity

/-- The concrete construction supplies fixed executable code directly.
Semantic certificates occur only in the result type and erased typing proof;
expanding the constructor also erases the instance-family argument at call sites. -/
@[macro_inline] def logicDerivation
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed)) :
    CryptoLogic.Derivation (ElGamal.Logic.signature chooseNormalizer)
      (ElGamal.Logic.context chooseNormalizer F) .indCPA F :=
  CryptoLogic.Derivation.transport
    (L := ElGamal.Logic.language Machine.ChooseSafeValidation.program
      Machine.FramedProductSafeMultiply.program)
    (S := ElGamal.Logic.signature chooseNormalizer)
    (Γ := ElGamal.Logic.context chooseNormalizer F)
    (ElGamal.Logic.reductionExpr Machine.ChooseSafeValidation.program
      Machine.FramedProductSafeMultiply.program) F
    (CryptoLogic.Derivation.hypothesis
      (L := ElGamal.Logic.language Machine.ChooseSafeValidation.program
        Machine.FramedProductSafeMultiply.program)
      (S := ElGamal.Logic.signature chooseNormalizer)
      (Γ := ElGamal.Logic.context chooseNormalizer F)
      ⟨0, by change 0 < 1; decide⟩)

/-- Recovering the executable compiler does not evaluate the family or interpretation. -/
theorem logicDerivation_compiler
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed)) :
    (logicDerivation F).compiler = logicCompiler := rfl

/-- The concrete security theorem recovered through generic logical soundness.
The only cryptographic premise is the existing machine-class DDH assumption. -/
theorem secureINDCPA_of_secureDDH_logic
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed))
    (hDDH : SecureOnWithin (representedDDHGoal sampling Domain embed)
      (representedDDHInterface sampling Domain embed
        simulatorPrimitives.instanceCode
        (fun n x => (simulatorPrimitives.elementCode n x).triple)).pptClass
      ((representedReduction sampling Domain embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling Domain embed)
      (representedINDCPAElementPPTClass sampling Domain embed
        simulatorPrimitives.instanceCode simulatorPrimitives.elementCode) F :=
  (logicDerivation F).sound_of_selected hDDH

theorem logicDerivation_compiler_run
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed))
    (p : Machine.Program) :
    (logicDerivation F).compiler.run p = chooseNormalizer.simulatorCode p := rfl

theorem logicDerivation_halts
    (F : InstanceFamily (representedINDCPAGoal sampling Domain embed))
    (p : CryptoLogic.BoundedProgram) (input : List Bool) :
    Machine.HaltsWithin (chooseNormalizer.simulatorCode p.program) input
      (((logicDerivation F).runBounded p).budget input.length) :=
  (logicDerivation F).compiler_halts p input

end ElGamal.PrimeOrderRepresentation
