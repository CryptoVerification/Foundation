import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivateKeyGeneration

namespace Foundation.Symmetric.EncryptThenMAC.PrivateKeyGenerationExamples
open Machine
set_option maxHeartbeats 1000000

def observed (coin : Bool) (markers : List Bool) (fuel : Nat) :=
  let (final, used) := PrivateKeyGeneration.simulate coin fuel (PrivateKeyGeneration.initial markers)
  ((PrivateKeyGeneration.readyStore final).map (fun (tape : Tape) => (tape.bits, tape.current)), used)

#guard observed false [true, true, true, true] 28 == (some ([false, false, false, false], some false), 28)
#guard observed true [true, true, true, true] 28 == (some ([true, true, true, true], some true), 28)
#guard observed false [true, true, true, true] 27 == (none, 27)
#guard observed false [] 4 == (some ([], none), 4)
#guard observed true [] 3 == (none, 3)
#guard observed true [false, true, false, false] 100 == (some ([true, true, true, true], some true), 28)
#guard observed true [true, true, true, true] 100 == observed true [true, true, true, true] 28

-- Pass the generated physical store directly to response preparation. No
-- whole-key conversion to a new tape is performed between these operations.
#guard [false, true].all fun coin =>
  let (generated, _) := PrivateKeyGeneration.simulate coin 28
    (PrivateKeyGeneration.initial [true, true, true, true])
  match PrivateKeyGeneration.readyStore generated with
  | none => false
  | some tape =>
      let start := ResponseHandoff.Control.headerWriting tape [true, true] {}
      let (final, used) := ResponseHandoff.simulate 80 start
      ResponseHandoff.publicPacket final == some [true, true, coin, coin] && used == 80 &&
        (ResponseHandoff.keyStore final).bits == [coin, coin, coin, coin]

-- Stopping the clock one transition before the ready state fails the
-- universal completion certificate, even though all key bits already exist.
example : ¬ PrivateKeyGeneration.ReadyWithin
    (PrivateKeyGeneration.initial [true, true, true, true]) 27 :=
  PrivateKeyGeneration.not_ready_before _

end Foundation.Symmetric.EncryptThenMAC.PrivateKeyGenerationExamples
