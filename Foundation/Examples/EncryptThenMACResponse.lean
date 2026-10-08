import Foundation.Constructions.Symmetric.EncryptThenMAC.AuthenticateResponse
import Foundation.Examples.OneTimePadNative

namespace Foundation.Symmetric.EncryptThenMAC.ResponseExamples
open Machine Foundation.Symmetric.OneTimePadExamples

-- The successful response keeps its ciphertext and appends the selected tag.
/-- info: [(some [true, false, true, false], 30, [true, false, true, false, false, true]),
  (some [true, true, false, true], 30, [true, true, true, false, false, true])] -/
#guard_msgs in
#eval [false, true].map fun ciphertext =>
  runProgram AuthenticateResponse.code [true, ciphertext, true, false, false, true] false 30

-- Failure never runs the signer, even though private key rows are present.
/-- info: (some [false], 3, [false, true, false, false, true]) -/
#guard_msgs in
#eval runProgram AuthenticateResponse.code [false, true, false, false, true] false 30

/-- info: (none, 29, [true, true, true, false, false, true]) -/
#guard_msgs in
#eval runProgram AuthenticateResponse.code [true, true, true, false, false, true] false 29

-- Truncated packets have the separate all-input stopping guarantee.
/-- info: true -/
#guard_msgs in
#eval [[], [true], [false], [true, false, true]].all fun raw =>
  (runProgram AuthenticateResponse.code raw false (4 * raw.length + 8)).1.isSome

example {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    HaltsWithin AuthenticateResponse.code (AuthenticateResponse.input key ciphertext) (8 * width + 14) :=
  AuthenticateResponse.halts_typed key ciphertext

example (raw : List Bool) : HaltsWithin AuthenticateResponse.code raw (4 * raw.length + 8) :=
  AuthenticateResponse.boundedProgram.halts raw

end Foundation.Symmetric.EncryptThenMAC.ResponseExamples
