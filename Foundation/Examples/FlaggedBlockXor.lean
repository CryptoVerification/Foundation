import Foundation.Crypto.Semantics.Machine.FlaggedBlockXor
import Foundation.Crypto.Semantics.Machine.Masking

namespace Foundation.Examples.FlaggedBlockXor
open Machine

def run (key message : List Bool) (fuel : Nat) : Option (List Bool) × Nat :=
  let (out, used) := Masking.simulate (.native Machine.FlaggedBlockXor.code) false fuel
    (.running (Machine.FlaggedBlockXor.initial key message))
  match out with
  | .running c => (if c.halted then some c.outputBits else none, used)
  | _ => (none, used)

/-- info: (some [false, true, true], 80) -/
#guard_msgs in
#eval run [true, false, true] [true, true, false] 80

/-- info: (none, 79) -/
#guard_msgs in
#eval run [true, false, true] [true, true, false] 79

/-- info: (some [], 8) -/
#guard_msgs in
#eval run [] [] 8

end Foundation.Examples.FlaggedBlockXor
