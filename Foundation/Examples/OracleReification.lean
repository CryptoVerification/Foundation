import Foundation.Crypto.Semantics.Oracle.Reification

/-! A native random bit, one real oracle request, response transfer, and a
native halt. The packet semantics keeps the full output before the old
finished-bit controller would discard it. -/
namespace CryptoOracle.Interactive.ReificationExamples
open Reification

def code : Code := [.native (.randomBit .output), .call, .native .halt]

def oracle (state : Nat) (request : List Bool) : Nat × List Bool :=
  (state + 1, request.map (!·))

def observed (coin : Bool) (fuel : Nat) :=
  let result := Reification.simulate code oracle coin fuel (Configuration.initial 0 [])
  (packet result.1.control, result.1.state, result.1.reverseTrace.reverse, result.2)

/-- info: [(some [true], 1, [([false], [true])], 13), (some [false], 1, [([true], [false])], 13)] -/
#guard_msgs in
#eval [false, true].map fun coin => observed coin 13

-- One fewer transition leaves the native halt unexecuted.
/-- info: [(none, 1, [([false], [true])], 12), (none, 1, [([true], [false])], 12)] -/
#guard_msgs in
#eval [false, true].map fun coin => observed coin 12

-- A larger budget does not add fake work after native termination.
/-- info: true -/
#guard_msgs in
#eval [false, true].all fun coin => observed coin 13 == observed coin 100

-- The private oracle state and old transcript are carried, not supplied to
-- the reified adversary as input or as a hidden instruction selector.
/-- info: (some [true], 101, [([true, true], []), ([false], [true])], 13) -/
#guard_msgs in
#eval
  let result := Reification.simulate code oracle false 13
    { Configuration.initial 100 [] with reverseTrace := [([true, true], [])] }
  (packet result.1.control, result.1.state, result.1.reverseTrace.reverse, result.2)

example (fuel : Nat) : (packetProgram code fuel (.running (Machine.Configuration.initial []))).BoundedQueries fuel :=
  packet_program_queries code fuel _

-- Fuel exhaustion at 12 steps cannot satisfy the real completion contract.
example : ¬ Reification.HaltsWithin code (fun state request => PMF.pure (oracle state request))
    (Configuration.initial 0 []) 12 := by
  intro h
  have hm := simulate_mem_support code oracle false 12 (Configuration.initial 0 [])
  have ht : terminal (Reification.simulate code oracle false 12 (Configuration.initial 0 [])).1.control = false := by
    decide
  have hc := h _ hm
  rw [ht] at hc
  contradiction

end CryptoOracle.Interactive.ReificationExamples
