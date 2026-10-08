import Foundation.Crypto.Semantics.Oracle.CounterMasking

namespace CryptoOracle.CounterMaskingExamples
open CounterMasking

-- One finite native attack forms an interleaved pair, calls the encryption
-- oracle, and reads the ciphertext after its public flag and unary counter.
def attack : Interactive.Code :=
  [.native (.write .output false), .native (.moveRight .output),
   .native (.write .output true), .native (.moveLeft .output), .call,
   .native (.moveRight .output), .native (.moveRight .output), .native .halt]

def pad (request : List Bool) : List Bool := [request.headD false]

/-- info: (some false, 39, 1, 1, [([false], [false])], [([false, true], [true, false, false])]) -/
#guard_msgs in
#eval
  let (out, used) := simulate (compile false attack) pad false 100 (initial [] [true, true])
  (result out, used, out.counter.length, out.capacity.length,
    out.reverseTrace.reverse, out.source.reverseTrace.reverse)

/-- info: (some true, 39, 1, 1, [([false], [false])], [([false, true], [true, false, true])]) -/
#guard_msgs in
#eval
  let (out, used) := simulate (compile true attack) pad false 100 (initial [] [true, true])
  (result out, used, out.counter.length, out.capacity.length,
    out.reverseTrace.reverse, out.source.reverseTrace.reverse)

/-- info: (none, 38) -/
#guard_msgs in
#eval
  let (out, used) := simulate (compile true attack) pad false 38 (initial [] [true, true])
  (result out, used)


/-- info: true -/
#guard_msgs in
#eval match Encodable.decode (α := Code)
    (Encodable.encode (compile true [.native .halt])) with
  | some decoded => decoded == compile true [.native .halt]
  | none => false

end CryptoOracle.CounterMaskingExamples
