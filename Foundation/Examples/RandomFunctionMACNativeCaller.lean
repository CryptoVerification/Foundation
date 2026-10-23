import Foundation.Constructions.Symmetric.RandomFunctionMACNativeExecution

/-! Concrete path checks for the full caller. These cover both attacker coin
choices, both parity branches, success/failure, and consistent/inconsistent
repeated responses. They do not replace universal correctness, halting or
service-time proofs for the 8-message/256-tag experiment.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Examples
open CryptoOracle CryptoOracle.Interactive Foundation.Probability
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

structure Scenario where
  coin : Bool
  odd : Bool
  wins : Bool
  cached : Bool
  deriving DecidableEq, Repr

def scenarios : List Scenario :=
  [false, true].flatMap fun coin => [false, true].flatMap fun odd =>
    [false, true].flatMap fun wins => [false, true].map fun cached => ⟨coin, odd, wins, cached⟩

def firstTag (scenario : Scenario) : Tag := if scenario.odd then 3 else 2
def repeatedTag (scenario : Scenario) : Tag := if scenario.cached then firstTag scenario else 17
def candidateTag (scenario : Scenario) : Tag := if scenario.coin then repeatedTag scenario else 33

/-- Explicit deterministic service used only to exercise the real code.
Every call increments state, so silently dropping a repeated call is detected. -/
def replies (scenario : Scenario) (count : Nat) (_ : List Bool) : Nat × List Bool :=
  let tag : Tag := match count with
    | 0 => firstTag scenario
    | 1 => 33
    | 2 => repeatedTag scenario
    | _ => if scenario.wins then candidateTag scenario else 255
  (count + 1, encodeTag tag)

def execution (scenario : Scenario) : Configuration Nat × Nat :=
  Reification.simulate Native.code (replies scenario) scenario.coin 500
    (Configuration.initial 0 [])

def decision (control : Control) : Bool := match control with
  | .running machine => machine.outputTape.current.getD false
  | _ => false

def check (scenario : Scenario) : Bool :=
  let result := execution scenario
  Reification.terminal result.1.control &&
    (decision result.1.control == scenario.wins) &&
    (result.1.state == 4) &&
    (result.1.reverseTrace.reverse.map Prod.fst ==
      [encodeMessage (firstMessage scenario.coin), encodeMessage (secondMessage (firstTag scenario)),
       encodeMessage (firstMessage scenario.coin), encodeMessage 7]) &&
    decide (result.2 ≤ 343)

theorem sixteen_paths_checked : scenarios.length = 16 ∧ scenarios.all check = true := by
  constructor
  · decide_cbv
  · simp only [scenarios, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
    repeat' constructor

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Examples
