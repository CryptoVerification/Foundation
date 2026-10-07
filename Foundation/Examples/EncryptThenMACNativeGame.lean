import Foundation.Constructions.Symmetric.EncryptThenMAC.NativePrivacyGame

namespace Foundation.Symmetric.EncryptThenMAC.NativeGameExamples
open Machine CryptoOracle PrivacyGameCodec NativePrivacyGame

-- Request decoding is total, including absent cells and trailing data.
example : request [] = (false, false) := rfl
example : request [true] = (true, false) := rfl
example : request [false, true, true] = (false, true) := rfl
example : PrivacyMachine.decodeCiphertext (ciphertext none) = none := rfl

-- The output convention observes the current cell, even when another bit
-- was written earlier on the output tape.
example : guess (.running { Configuration.initial [] with
    halted := true, outputTape := { left := [some true], current := none, right := [] } }) = false := rfl
example : guess (.running { Configuration.initial [] with
    halted := true, outputTape := { left := [], current := some true, right := [] } }) = true := rfl

def haltCode : Interactive.Code := [.native .halt]

theorem halt_stops (width : Nat → Nat) (n : Nat) (key side : Bool) (input : List Bool) :
    SourceStops width n key side haltCode 1 input := by
  intro macKey hKey final hFinal
  simp [Interactive.Reification.eval, Interactive.Reification.terminal,
    Interactive.step, Interactive.transition, haltCode,
    PrivacyMachine.logicalInitial, PrivacyMachine.LogicalFrame.view,
    Configuration.initial, Instruction.next] at hFinal
  subst final
  rfl

-- The stopping hypothesis is discharged from actual source instructions;
-- the generic equality includes the native private-key sampler.
example (width : Nat → Nat) (n : Nat) (side : Bool) (input : List Bool) :
    game width n side haltCode 1 input =
      encryptionGame OneBitEncryption.scheme n side
        (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n
          (attack width n haltCode 1 input)) :=
  game_eq_encryption width n side haltCode 1 input (fun key _ => halt_stops width n key side input)

example (width : Nat → Nat) (n : Nat) (key side : Bool) (input : List Bool) :
    PrivacyMachine.HaltsWithin haltCode (byteEncryptionOracle n key side)
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) input)
      (PrivacyMachine.executionBudget (width n) 1) :=
  halts width n key side haltCode 1 input (halt_stops width n key side input)

end Foundation.Symmetric.EncryptThenMAC.NativeGameExamples
