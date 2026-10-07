import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyMachine

namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachineExamples
open Machine PrivacyMachine

-- First send [false,true]. The immediate second call is adaptive: it sends
-- the entire authenticated response from the first call as its new request.
def code : Source.Code :=
  [.native (.write .output false), .native (.moveRight .output),
   .native (.write .output true), .native (.moveLeft .output),
   .call, .call, .native .halt]

-- A fixed encryption key false, right-side choice, and one successful use.
-- Query counting belongs to the external oracle; native code cannot read it.
def oracle (state : Nat) (request : List Bool) : Nat × List Bool :=
  (state + 1, if state == 0 then [true, Bool.xor false (request[1]?.getD false)] else [false])

def keyBits : Control → Option (List Bool)
  | .source key _ => some key.bits
  | _ => none

def observed (coin : Bool) (fuel : Nat) :=
  let (final, used) := simulate code oracle coin fuel (initial 0 [true, true, true, true] [])
  (publicPacket final.control, used, final.state,
    final.sourceTrace.reverse, final.externalTrace.reverse, keyBits final.control)

#guard observed false 225 ==
  (some [false], 225, 2,
    [([false, true], [true, true, false, false]), ([true, true, false, false], [false])],
    [([false, true], [true, true]), ([true, true, false, false], [false])], some [false, false, false, false])
#guard observed true 225 ==
  (some [false], 225, 2,
    [([false, true], [true, true, true, true]), ([true, true, true, true], [false])],
    [([false, true], [true, true]), ([true, true, true, true], [false])], some [true, true, true, true])
#guard (observed false 224).1 == none
#guard [false, true].all fun coin => observed coin 1000 == observed coin 225

-- Distinct table rows: the observed first response contains only the row
-- selected by ciphertext true, while both private rows remain intact.
#guard
  let start : Frame Nat := ⟨0, .source (Tape.ofBits [true, false, false, true])
    (.running (Configuration.initial [])), [], []⟩
  let (final, _) := simulate code oracle false 1000 start
  final.sourceTrace.reverse == [([false, true], [true, true, false, true]), ([true, true, false, true], [false])] &&
    keyBits final.control == some [true, false, false, true]

-- Attempt to read a secret through the source input tape: the source sees
-- its own blank input, irrespective of generated private key bits.
def probe : Source.Code :=
  [.native (.branch .input 1 3 3), .native (.write .output false), .native .halt,
   .native (.write .output true), .native .halt]

#guard [false, true].all fun coin =>
  let (final, _) := simulate probe oracle coin 100 (initial 0 [true, true, true, true] [])
  publicPacket final.control == some [false] && final.state == 0 &&
    final.sourceTrace == [] && final.externalTrace == []

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachineExamples
