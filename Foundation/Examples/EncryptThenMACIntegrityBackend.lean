import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityBackend
import Foundation.Examples.EncryptThenMACIntegrityGame

namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackendExamples
open CryptoLogic.General CryptoOracle IntegrityBackend IntegrityGameCodec

def profile : Profile := ⟨fun _ => 1, fun _ => []⟩
def width (_ : Nat) : Nat := 2

noncomputable def sourceWitness : (sourceObject width).Witness (fun _ => ())
    (fun n => attack width n IntegrityGameExamples.haltCode 1 []) where
  code := IntegrityGameExamples.haltCode
  resources := profile
  executes := ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
    fun n macKey _ => IntegrityGameExamples.halt_stops width n macKey []⟩
  realizes := by intro n; rfl
  admissible := ⟨IntegrityGameExamples.haltCode, profile,
    ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
      fun n macKey _ => IntegrityGameExamples.halt_stops width n macKey []⟩,
    by intro n; rfl⟩

-- This is an inhabited operational certificate, including real private-key
-- sampling, not a vacuous class defined by impossible execution evidence.
example : TargetExecutes width (compiler.run sourceWitness.code) profile :=
  (certificate width).compiler_executes _ _ sourceWitness

example : TargetRealizes width ((transform width).mapFamily (fun _ => ()))
    ((transform width).mapAdversaryFamily (fun _ => ())
      (fun n => attack width n IntegrityGameExamples.haltCode 1 []))
    (compiler.run sourceWitness.code) profile :=
  (certificate width).compiler_realizes _ _ sourceWitness

example : ((certificate width).mapWitness _ _ sourceWitness).code.source =
    IntegrityGameExamples.haltCode := rfl

example (n : Nat) :
    IntegrityMachine.executionBudget (width n)
      (((certificate width).mapWitness _ _ sourceWitness).resources.count n) = 49 := rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackendExamples
