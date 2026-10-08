import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityGameObservation

namespace Foundation.Symmetric.EncryptThenMAC.IntegrityGameExamples
open Machine Foundation.Probability CryptoOracle IntegrityGameCodec IntegrityGameObservation

def haltCode : Interactive.Code := [.native .halt]

theorem halt_stops (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n)) (input : List Bool) :
    SourceStops width n macKey haltCode 1 input := by
  intro key hKey final hFinal
  simp [Interactive.Reification.eval, Interactive.Reification.terminal,
    Interactive.step, Interactive.transition, haltCode,
    IntegrityMachine.logicalInitial, IntegrityMachine.LogicalFrame.view,
    Configuration.initial, Instruction.next] at hFinal
  subst final
  rfl

-- Supply actual source termination, then apply both typed realization and
-- the real whole-machine stopping theorem, for every MAC key and input.
example (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n)) (input : List Bool) :
    (IntegrityMachine.eval haltCode (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) 1) (IntegrityMachine.initial () input)).map
        (nativeOutcome (width n)) =
      sampleBit.bind (fun key => (attack width n haltCode 1 input).run
        (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey) false) :=
  execution_outcome width n macKey haltCode 1 input (halt_stops width n macKey input)

example (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n)) (input : List Bool) :
    IntegrityMachine.HaltsWithin haltCode (byteSigningOracle macKey) (IntegrityMachine.initial () input)
      (IntegrityMachine.executionBudget (width n) 1) :=
  execution_halts width n macKey haltCode 1 input (halt_stops width n macKey input)

example : decodeResponse 2 [false, true, true] = none := rfl
example : decodeResponse 0 [true, false] = some (false, fun i => Fin.elim0 i) := by
  have h : decodeTag 0 [] = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  exact congrArg (fun tag => some (false, tag)) h

end Foundation.Symmetric.EncryptThenMAC.IntegrityGameExamples
