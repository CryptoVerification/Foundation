import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMAC
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitEncryption
import Foundation.Examples.OneTimePadNative

/-! The concrete authentication primitive is tested on the native transition
interpreter, including the exact valid-input budget and malformed packets. -/
namespace Foundation.Symmetric.EncryptThenMAC.TableExamples
open Machine Foundation.Symmetric.OneTimePadExamples

-- Ciphertexts choose different rows of the same two-entry secret table.
/-- info: [(some [true, false], 20, [false, true, false, false, true]),
  (some [false, true], 20, [true, true, false, false, true])] -/
#guard_msgs in
#eval [false, true].map fun side =>
  runProgram TableMAC.Native.signCode [side, true, false, false, true] false 20

-- Reducing the budget by one really leaves the signer unfinished.
/-- info: (none, 19, [true, true, false, false, true]) -/
#guard_msgs in
#eval runProgram TableMAC.Native.signCode [true, true, false, false, true] false 19

-- Empty-width keys, missing ciphertexts, and incomplete row pairs terminate.
/-- info: [(some [], 2, []), (some [], 4, [true]), (some [], 6, [false, true]), (some [], 6, [true, false])] -/
#guard_msgs in
#eval [[], [true], [false, true], [true, false]].map fun raw =>
  runProgram TableMAC.Native.signCode raw false (4 * raw.length + 6)

-- Exhaust all eight choices of a ciphertext and a one-bit key pair.
/-- info: true -/
#guard_msgs in
#eval [false, true].all fun side => [false, true].all fun first =>
  [false, true].all fun second =>
    (runProgram TableMAC.Native.signCode [side, first, second] false 12).1 ==
      some [if side then second else first]

-- Exhaust all eight choices, including the exhausted-key branch. Actual
-- transitions are 12 on successful encryption and 6 on exhaustion.
/-- info: true -/
#guard_msgs in
#eval [false, true].all fun used => [false, true].all fun key =>
  [false, true].all fun message =>
    let result := runProgram OneBitEncryption.Native.encryptionCode [used, key, message] false 12
    result.1 == some (OneBitEncryption.Native.output used key message) &&
      result.2.1 == (if used then 6 else 12)

/-- info: [(some [false], 2, []), (some [true], 2, [])] -/
#guard_msgs in
#eval [false, true].map fun coin => runProgram OneBitEncryption.Native.keygenCode [] coin 2

/-- info: [(none, 11, [false, true, false]), (none, 5, [true, true, false])] -/
#guard_msgs in
#eval [(false, 11), (true, 5)].map fun (used, fuel) =>
  runProgram OneBitEncryption.Native.encryptionCode [used, true, false] false fuel

example (raw : List Bool) : HaltsWithin TableMAC.Native.signCode raw (4 * raw.length + 6) :=
  TableMAC.Native.signProgram.halts raw

example {width : Nat} (key : TableMAC.Key width) (ciphertext : Bool) :
    evalWithin TableMAC.Native.signCode (TableMAC.Native.input key ciphertext) (8 * width + 4) =
      PMF.pure (some (TableMAC.sign key ciphertext).toList) :=
  TableMAC.Native.sign_correct key ciphertext

end Foundation.Symmetric.EncryptThenMAC.TableExamples
