import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivateKeyCopy
import Foundation.Examples.OneTimePadNative

namespace Foundation.Symmetric.EncryptThenMAC.PrivateCopyExamples
open Machine PrivateKeyCopy

def simulate (start : Configuration) (fuel : Nat) : Configuration × Nat :=
  let (result, used) := Masking.simulate (.native code) false fuel (.running start)
  match result with
  | .running final => (final, used)
  | _ => (start, used)

def observed (key header : List Bool) (fuel : Nat) :=
  let (final, used) := simulate (copying [] key (header.reverse.map some)) fuel
  (if final.halted then some final.outputBits else none, used,
    final.inputTape.bits, final.inputTape.current)

-- The private prefix is already present before this operation begins. Its
-- earlier preparation is not included in the copy routine's transition bound.
#guard observed [true, false, false, true] [true, false] 37 ==
  (some [true, false, true, false, false, true], 37, [true, false, false, true], some true)
#guard (observed [true, false, false, true] [true, false] 36).1 == none
#guard observed [] [true, false] 5 == (some [true, false], 5, [], none)

#guard [[], [false], [true], [false, true], [true, false, true]].all fun key =>
  let out := observed key [false] (8 * key.length + 20)
  out == (some (false :: key), 8 * key.length + 5, key, key.head?)

-- Keep the physical key tape returned by the first call. Supply a fresh
-- private output buffer for the second call; no key tape reset is performed.
#guard
  let key := [true, false, false, true]
  let (first, firstUsed) := simulate (copying [] key []) 37
  let start : Configuration := { inputTape := first.inputTape, outputTape := { left := [some false, some true] } }
  let (second, secondUsed) := simulate start 37
  firstUsed == 37 && secondUsed == 37 && second.halted &&
    second.inputTape.bits == key && second.inputTape.current == some true &&
    second.outputBits == [true, false, true, false, false, true]

example (key header : List Bool) :
    (evalConfigWithin code
      { inputTape := (finish key []).inputTape, outputTape := { left := header.reverse.map some } } (8 * key.length + 5)).map
      (fun final => (final.halted, final.inputTape.bits, final.outputBits)) =
        PMF.pure (true, key, header ++ key) :=
  reusable_run key header _ (key_restored key [])

end Foundation.Symmetric.EncryptThenMAC.PrivateCopyExamples
