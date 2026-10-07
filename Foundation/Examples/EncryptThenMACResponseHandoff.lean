import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoff

namespace Foundation.Symmetric.EncryptThenMAC.HandoffExamples
open Machine ResponseHandoff

def rawStart (rows : List Bool) (ciphertext : Option Bool) : Control :=
  .copying (PrivateKeyCopy.copying [] rows ((header ciphertext).reverse.map some))

def observed (rows : List Bool) (ciphertext : Option Bool) (fuel : Nat) :=
  let (final, used) := simulate fuel (rawStart rows ciphertext)
  (publicPacket final, used, (keyStore final).bits, (keyStore final).current)

#guard observed [true, false, false, true] (some false) 75 ==
  (some [true, false, true, false], 75, [true, false, false, true], some true)
#guard observed [true, false, false, true] (some true) 75 ==
  (some [true, true, false, true], 75, [true, false, false, true], some true)
#guard (observed [true, false, false, true] (some true) 74).1 == none
#guard observed [true, false, false, true] (some true) 100 ==
  observed [true, false, false, true] (some true) 75
#guard observed [true, false, false, true] none 100 ==
  (some [false], 47, [true, false, false, true], some true)
#guard observed [] (some true) 23 == (some [true, true], 23, [], none)

-- The complete entry includes writing and advancing over both header bits.
#guard
  let start := Control.headerWriting (Tape.ofBits [true, false, false, true]) [true, true] {}
  let (final, used) := simulate 80 start
  publicPacket final == some [true, true, false, true] && used == 80 &&
    (keyStore final).bits == [true, false, false, true]
#guard
  let start := Control.headerWriting (Tape.ofBits [true, false, false, true]) [true, true] {}
  publicPacket (simulate 79 start).1 == none
#guard
  let start := Control.headerWriting (Tape.ofBits [true, false, false, true]) [false] {}
  let (final, used) := simulate 77 start
  publicPacket final == some [false] && used == 50

-- All 16 interleaved two-row keys, for each of the two ciphertext bits.
#guard (List.range 16).all fun value =>
  let rows := List.ofFn (fun i : Fin 4 => value / (2 ^ i.val) % 2 == 1)
  [false, true].all fun ciphertext =>
    observed rows (some ciphertext) 75 ==
      (some ([true, ciphertext] ++ TableMAC.Native.selectedPairs ciphertext rows),
        75, rows, rows.head?)

-- Even when the copy buffer already contains the entire key, no packet is
-- public during copying or rewinding. Authentication owns a separate output.
#guard
  let completed := .copying (PrivateKeyCopy.finish [true, false, false, true] [some true, some true])
  publicPacket completed == none && publicPacket (simulateStep completed) == none

-- Use the retained physical key tape again, without replacing it by ofBits.
#guard
  let (first, _) := simulate 75 (rawStart [true, false, false, true] (some false))
  let secondStart := Control.copying ({ inputTape := keyStore first, outputTape := { left := [some true, some true] } } : Configuration)
  let (second, used) := simulate 75 secondStart
  publicPacket second == some [true, true, false, true] && used == 75 &&
    (keyStore second).bits == [true, false, false, true] && (keyStore second).current == some true

example {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    StopsWithin (starting key ciphertext) ((8 * (keyBytes key).length + 5) +
      ((keyBytes key).length + (header ciphertext).length + 2 + (8 * width + 14))) :=
  full_response_stops key ciphertext

end Foundation.Symmetric.EncryptThenMAC.HandoffExamples
