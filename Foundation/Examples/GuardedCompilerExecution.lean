import Foundation.Crypto.Semantics.Machine.GuardedCompiler

namespace Machine.GuardedCompiler.Examples

/- Exercise the public entry point: csimp must select the stack-safe version.
Check instruction order, relocated control flow, padding, and the final halt. -/
/-- info: true -/
#guard_msgs in
#eval
  let code := compile [.jump 1, .halt]
  code.length == 137 && code[0]? == some (.jump 68) &&
    code[67]? == some .halt && code[68]? == some .halt &&
    code[136]? == some .halt

/- A long source produces 6,800,000 instructions. The public specification
is evaluated through the proved compiler replacement, not called directly
through blocksTR. Both endpoints and a nonzero initial source address are checked. -/
/-- info: true -/
#guard_msgs in
#eval
  let count := 100000
  let code := blocks (count + 7) 7 (List.replicate count (.jump (count + 8)))
  code.length == 68 * count &&
    code[0]? == some (.jump (68 * (count + 7))) &&
    code[68 * (count - 1)]? == some (.jump (68 * (count + 7))) &&
    code[68 * count - 1]? == some .halt

end Machine.GuardedCompiler.Examples
