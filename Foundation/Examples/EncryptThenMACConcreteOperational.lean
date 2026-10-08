import Foundation.Constructions.Symmetric.EncryptThenMAC.ConcreteOperational
import Foundation.Examples.EncryptThenMACNativeGame
import Foundation.Examples.EncryptThenMACIntegrityGame

namespace Foundation.Symmetric.EncryptThenMAC.ConcreteOperationalExamples
open CryptoLogic.General CryptoOracle ConcreteOperational
open scoped ENNReal

def width (_ : Nat) : Nat := 2

def code : SourceCode := (NativeGameExamples.haltCode, IntegrityGameExamples.haltCode)
def profile : Profile := (⟨fun _ => 1, fun _ => []⟩, ⟨fun _ => 1, fun _ => [true]⟩)

noncomputable def attacks : AdversaryFamily
    (goal OneBitEncryption.scheme (TableMAC.scheme width)) (fun _ => ()) :=
  fun n => (PrivacyGameCodec.attack width n code.1 1 [],
    IntegrityGameCodec.attack width n code.2 1 [true])

theorem executes : SourceExecutes width code profile := by
  constructor
  · exact ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
      fun n side key _ => NativeGameExamples.halt_stops width n key side []⟩
  · exact ⟨PolynomiallyBounded.const 2, PolynomiallyBounded.const 1,
      fun n macKey _ => IntegrityGameExamples.halt_stops width n macKey [true]⟩

theorem realizes : SourceRealizes width (fun _ => ()) attacks code profile :=
  ⟨fun _ => rfl, fun _ => rfl⟩

noncomputable def sourceWitness : (sourceBackend width).object.Witness (fun _ => ()) attacks where
  code := code
  resources := profile
  executes := executes
  realizes := realizes
  admissible := ⟨code, profile, executes, realizes⟩

example : ((realization width).encryptionWitness _ _ sourceWitness).code.source = code.1 := rfl
example : ((realization width).macWitness _ _ sourceWitness).code.source = code.2 := rfl
example : ((realization width).encryptionWitness _ _ sourceWitness).resources.input 0 = [] := rfl
example : ((realization width).macWitness _ _ sourceWitness).resources.input 0 = [true] := rfl

-- Both exact emitted programs carry actual stopping and game witnesses.
example := (realization width).compiled_executes attacks sourceWitness
example := (realization width).compiled_realizes attacks sourceWitness
example := translated_witnesses width attacks sourceWitness

example (n : Nat) :
    PrivacyMachine.executionBudget (width n)
      (((realization width).encryptionWitness _ _ sourceWitness).resources.count n) = 126 ∧
    IntegrityMachine.executionBudget (width n)
      (((realization width).macWitness _ _ sourceWitness).resources.count n) = 49 := ⟨rfl, rfl⟩

-- Test pure compilation on distinct instruction sequences. There is no
-- semantic model, key sampler, or stopping certificate in this evaluation.
def summary : Sigma system.Code → Kind × Nat
  | ⟨.authenticated, code⟩ => (.authenticated, code.1.length + code.2.length)
  | ⟨.encryption, code⟩ => (.encryption, code.source.length)
  | ⟨.mac, code⟩ => (.mac, code.source.length)

/-- info: true -/
#guard_msgs in
#eval
  ((Operational.plan encryptionCompiler macCompiler (Logic.expansion.translate Logic.proof)).run
    ([.native .halt], [.native (.write .output true), .native .halt])).map
      (fun entry => (entry.1.val, summary entry.2)) ==
    [(0, Kind.encryption, 1), (1, Kind.mac, 2)]

-- Distinct base assumptions bound the represented source attack class.
example (ε δ : Nat → ℝ≥0∞)
    (hE : BoundedByOnWithin (encryptionGoal OneBitEncryption.scheme)
      (encryptionBackend width).adversaries (fun _ => ()) ε)
    (hM : BoundedByOnWithin (macGoal OneBitEncryption.scheme (TableMAC.scheme width))
      (macBackend width).adversaries (fun _ => ()) δ) :
    BoundedByOnWithin (goal OneBitEncryption.scheme (TableMAC.scheme width))
      (sourceBackend width).adversaries (fun _ => ()) (fun n => ε n + δ n) :=
  bounded width ε δ hE hM

end Foundation.Symmetric.EncryptThenMAC.ConcreteOperationalExamples
