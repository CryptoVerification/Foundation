import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyResponseLayout

namespace Foundation.Symmetric.EncryptThenMAC.OutputLayoutExamples
open Machine

def key : TableMAC.Key 2 := (fun i => i.val == 0, fun i => i.val == 1)

def nativeLayout (privateInput : Tape) :=
  let (result, used) := Masking.simulate (.native AuthenticateResponse.code) false 30
    (.running { inputTape := privateInput })
  match result with
  | .running final => (final.halted, final.outputTape, used)
  | _ => (false, {}, used)

-- Success stops on a blank after four response bits. Failure stops on its
-- sole bit. Input blank padding changes neither of those physical layouts.
#guard nativeLayout (Tape.ofBits (AuthenticateResponse.input key (some true))) ==
  (true, AuthenticateResponse.responseTape key (some true), 30)
#guard nativeLayout (Tape.ofBits (AuthenticateResponse.input key none)) ==
  (true, AuthenticateResponse.responseTape key none, 3)

#guard [none, some false, some true].all fun ciphertext =>
  let canonical := Tape.ofBits (AuthenticateResponse.input key ciphertext)
  let padded : Tape := { canonical with left := [none, none], right := canonical.right ++ [none, none] }
  nativeLayout padded == nativeLayout canonical

-- The callback return preserves the suspended source machine and both
-- traces. The authenticated response is queued for public output loading.
#guard
  let source : Configuration := { pc := 6, inputTape := Tape.ofBits [false, true], outputTape := Tape.ofBits [true, false] }
  let privateKey := Tape.ofBits [true, false, false, true]
  let request := [false, true]
  let start : PrivacyMachine.Frame Nat := ⟨100,
    .rewinding privateKey source request (AuthenticateResponse.responseTape key (some true)),
    [([true], [false])], [([false], [true])]⟩
  let (final, used) := PrivacyMachine.simulate [] (fun state _ => (state + 1, [])) false 15 start
  match final.control with
  | .source retained (.loading suspended response _) =>
      used == 15 && retained == privateKey && suspended == source && response == [true, true, false, true] &&
        final.state == 100 && final.sourceTrace == [(request, response), ([true], [false])] &&
        final.externalTrace == [([false], [true])]
  | _ => false

example (ciphertext : Option Bool) : PrivacyMachine.responseOverhead 2 ciphertext ≤ 96 :=
  PrivacyMachine.responseOverhead_le 2 ciphertext

end Foundation.Symmetric.EncryptThenMAC.OutputLayoutExamples
