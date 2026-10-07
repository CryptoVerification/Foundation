import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityResponse

namespace Foundation.Symmetric.EncryptThenMAC.IntegrityResponseExamples
open Machine IntegrityMachine

def code : SourceCode := [.native .halt]
def oracle (state : Nat) (_ : Bool) : Nat × List Bool := (state + 1, [])

-- Test empty and nonuniform tags, including the resumed source loader and
-- native halt. Starting after signing must not invoke the oracle again.
#guard [[], [false], [true, false, true]].all fun tag =>
  [false, true].all fun ciphertext =>
    let source := Configuration.initial [true, false]
    let start : Frame Nat := ⟨7, .header true source [false] ciphertext tag 0 {},
      [([true], [false])], [(false, [true])]⟩
    let (final, used) := simulate code oracle false 1000 start
    match final.control with
    | .source key exhausted (.running machine) =>
        terminal final.control && key && exhausted &&
        machine.inputTape == source.inputTape &&
        publicPacket final.control == some (true :: ciphertext :: tag) &&
        final.state == 7 && final.signingTrace == start.signingTrace &&
        final.sourceTrace == ([false], true :: ciphertext :: tag) :: start.sourceTrace &&
        used == 8 * tag.length + 23
    | _ => false

#guard
  let source := Configuration.initial [true, false]
  let start : Frame Nat := ⟨7, .failure true source [true], [], [(false, [true])]⟩
  let (final, used) := simulate code oracle false 100 start
  terminal final.control && publicPacket final.control == some [false] && final.state == 7 &&
    final.signingTrace == start.signingTrace && final.sourceTrace == [([true], [false])] && used == 12

end Foundation.Symmetric.EncryptThenMAC.IntegrityResponseExamples
