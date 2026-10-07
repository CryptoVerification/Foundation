import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyBackend
import Foundation.Examples.EncryptThenMACNativeGame

namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackendExamples
open CryptoLogic.General CryptoOracle PrivacyBackend PrivacyGameCodec

def profile : Profile := ⟨fun _ => 1, fun _ => []⟩
def width (_ : Nat) : Nat := 2

noncomputable def sourceWitness : (sourceObject width).Witness (fun _ => ())
    (fun n => attack width n NativeGameExamples.haltCode 1 []) where
  code := NativeGameExamples.haltCode
  resources := profile
  executes := ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
    fun n side key _ => NativeGameExamples.halt_stops width n key side []⟩
  realizes := by intro n; rfl
  admissible := ⟨NativeGameExamples.haltCode, profile,
    ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
      fun n side key _ => NativeGameExamples.halt_stops width n key side []⟩,
    by intro n; rfl⟩

-- This is an inhabited operational certificate, including real private-key
-- sampling, not a vacuous class defined by impossible execution evidence.
example : TargetExecutes width (compiler.run sourceWitness.code) profile :=
  (certificate width).compiler_executes _ _ sourceWitness

example : TargetRealizes width ((transform width).mapFamily (fun _ => ()))
    ((transform width).mapAdversaryFamily (fun _ => ())
      (fun n => attack width n NativeGameExamples.haltCode 1 []))
    (compiler.run sourceWitness.code) profile :=
  (certificate width).compiler_realizes _ _ sourceWitness

example : ((certificate width).mapWitness _ _ sourceWitness).code.source =
    NativeGameExamples.haltCode := rfl

example (n : Nat) :
    PrivacyMachine.executionBudget (width n)
      (((certificate width).mapWitness _ _ sourceWitness).resources.count n) = 126 := rfl

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackendExamples
