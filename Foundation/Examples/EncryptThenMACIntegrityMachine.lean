import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityMachine

namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachineExamples
open Machine IntegrityMachine

def code : SourceCode :=
  [.native (.write .output false), .call, .call, .call, .call, .native .halt]

def oracle (count : Nat) (ciphertext : Bool) : Nat × List Bool :=
  (count + 1, [!ciphertext, ciphertext])

-- Four adaptive requests cause one signing call. The exhausted encryption
-- key fails the remaining three requests; neither signing state nor history
-- changes for those failures. The source retains its original input tape.
#guard [false, true].all fun coin =>
  let (final, used) := simulate code oracle coin 1000 (initial 0 [true])
  let firstResponse := [true, coin, !coin, coin]
  match final.control with
  | .source key exhausted (.running source) =>
      terminal final.control && key == coin && exhausted && source.halted &&
      source.inputTape == Tape.ofBits [true] && publicPacket final.control == some [false] &&
      final.state == 1 && final.signingTrace == [(coin, [!coin, coin])] &&
      final.sourceTrace.reverse == [([false], firstResponse), (firstResponse, [false]),
        ([false], [false]), ([false], [false])] &&
      used == 172 && (simulate code oracle coin 2000 (initial 0 [true])).2 == used
  | _ => false

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachineExamples
