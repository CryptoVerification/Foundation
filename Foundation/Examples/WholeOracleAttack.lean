import Foundation.Crypto.Semantics.Oracle.WholeAttack
import Foundation.Examples.OracleQueries

namespace CryptoOracle.Examples

open Foundation.Probability Machine
open scoped ENNReal

set_option maxHeartbeats 1000000

def wholeInterface : WholeInterface protocol where
  instanceEncoding _ := FiniteBitEncoding.unit
  requestEncoding := FiniteBitEncoding.bool
  responseEncoding := FiniteBitEncoding.bool
  fallbackRequest := false

/-- Four finite instructions implement both adaptive queries. The response
loaded by the first call becomes the second request; the second response is
the result. No host continuation is used to choose either query. -/
def adaptiveCode : Interactive.Code :=
  [.native (.write .output false), .call, .call, .native .halt]

def randomCode : Interactive.Code := [.native (.randomBit .output), .native .halt]

theorem randomCode_run (oracle : Interactive.BitOracle Nat) (input : List Bool) :
    Interactive.eval randomCode oracle (Interactive.Configuration.initial 0 input) 3 =
      sampleBit.map (fun bit =>
        (⟨0, .finished bit, []⟩ : Interactive.Configuration Nat)) := by
  simp [Interactive.eval, Interactive.step, Interactive.transition, randomCode,
    Interactive.Configuration.initial, Machine.Configuration.initial,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Tape.write, PMF.bind_map, Function.comp_def]
  congr 1
  funext bit
  cases bit <;>
    simp [Interactive.step, Interactive.transition]

example (oracle : Interactive.BitOracle Nat) (input : List Bool) :
    Interactive.HaltsWithin randomCode oracle (Interactive.Configuration.initial 0 input) 3 := by
  intro finish hFinish
  rw [randomCode_run, PMF.mem_support_map_iff] at hFinish
  obtain ⟨bit, _, hEq⟩ := hFinish
  subst finish
  exact ⟨bit, rfl⟩

def deterministicOracle (first : Bool) (state : Nat) (request : List Bool) :
    Nat × List Bool :=
  (state + 1, [if state = 0 then first else
    (FiniteBitEncoding.bool.decode request).getD false])

def loopingCode : Interactive.Code := [.native (.jump 0)]

theorem loopingCode_eval (oracle : Interactive.BitOracle Nat) (input : List Bool) (fuel : Nat) :
    Interactive.eval loopingCode oracle (Interactive.Configuration.initial 0 input) fuel =
      PMF.pure (Interactive.Configuration.initial 0 input) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Interactive.eval, ih, PMF.pure_bind]
      simp [Interactive.step, Interactive.transition, loopingCode,
        Interactive.Configuration.initial, Machine.Configuration.initial, Machine.Instruction.next]

example (oracle : Interactive.BitOracle Nat) (input : List Bool) (fuel : Nat) :
    ¬ Interactive.HaltsWithin loopingCode oracle (Interactive.Configuration.initial 0 input) fuel := by
  unfold Interactive.HaltsWithin
  rw [loopingCode_eval]
  simp [Interactive.Configuration.complete,
    Interactive.Configuration.initial]

/-- info: (none, 100000) -/
#guard_msgs in
#eval
  let (finish, used) := Interactive.simulate loopingCode (deterministicOracle false)
    false 100000 (Interactive.Configuration.initial 0 [])
  (finish.result, used)

/-- info: (some true, 25, 2, [([false], [true]), ([true], [true])]) -/
#guard_msgs in
#eval
  let (finish, used) := Interactive.simulate adaptiveCode (deterministicOracle true)
    false 100 (Interactive.Configuration.initial 0 [])
  (finish.result, used, finish.state, finish.reverseTrace.reverse)

/-- info: (some false, 25, 2, [([false], [false]), ([false], [false])]) -/
#guard_msgs in
#eval
  let (finish, used) := Interactive.simulate adaptiveCode (deterministicOracle false)
    false 100 (Interactive.Configuration.initial 0 [])
  (finish.result, used, finish.state, finish.reverseTrace.reverse)

/-- info: (none, 24) -/
#guard_msgs in
#eval
  let (finish, used) := Interactive.simulate adaptiveCode (deterministicOracle true)
    false 24 (Interactive.Configuration.initial 0 [])
  (finish.result, used)

set_option maxRecDepth 10000 in
theorem adaptiveCode_run (input : List Bool) (first : Bool) :
    Interactive.eval adaptiveCode (wholeInterface.bitOracle (countingOracle first))
      (Interactive.Configuration.initial 0 input) 25 =
    PMF.pure (⟨2, .finished first,
      [([first], [first]), ([false], [first])]⟩ : Interactive.Configuration Nat) := by
  cases first <;>
    simp [Interactive.eval, Interactive.step, Interactive.transition, adaptiveCode,
      Interactive.Configuration.initial, Machine.Configuration.initial,
      wholeInterface, WholeInterface.bitOracle, countingOracle,
      FiniteBitEncoding.bool, Machine.Instruction.next,
      Machine.Configuration.updateTape, Machine.Configuration.advance,
      Tape.write, Tape.moveRight, Tape.moveLeft, PMF.pure_map]

-- After 24 steps the native halt has happened, but result dispatch is unfinished.
set_option maxRecDepth 10000 in
example : ¬ Interactive.HaltsWithin adaptiveCode
    (wholeInterface.bitOracle (countingOracle true))
    (Interactive.Configuration.initial 0 []) 24 := by
  simp [Interactive.HaltsWithin, Interactive.eval, Interactive.step, Interactive.transition, adaptiveCode,
    Interactive.Configuration.initial, Machine.Configuration.initial,
    wholeInterface, WholeInterface.bitOracle, countingOracle,
    FiniteBitEncoding.bool, Machine.Instruction.next,
    Machine.Configuration.updateTape, Machine.Configuration.advance,
    Tape.write, Tape.moveRight, Tape.moveLeft, PMF.pure_map,
    Interactive.Configuration.complete]

noncomputable def adaptiveWholeWitness :
    WholeWitness wholeInterface (fun _ => 25) (fun _ => 2)
      (fun _ => ()) (fun _ => adaptive) where
  code := adaptiveCode
  halts := by
    intro n right
    cases right <;> intro finish hFinish
    all_goals
      change finish ∈ (Interactive.eval adaptiveCode
        (wholeInterface.bitOracle (countingOracle _))
        (Interactive.Configuration.initial 0 (wholeInterface.input n ())) 25).support at hFinish
      rw [adaptiveCode_run, PMF.mem_support_pure_iff] at hFinish
      subst finish
      exact ⟨_, rfl⟩
  queries := by
    intro n right
    cases right <;> intro finish hFinish
    all_goals
      change finish ∈ (Interactive.eval adaptiveCode
        (wholeInterface.bitOracle (countingOracle _))
        (Interactive.Configuration.initial 0 (wholeInterface.input n ())) 25).support at hFinish
      rw [adaptiveCode_run, PMF.mem_support_pure_iff] at hFinish
      subst finish
      change 2 ≤ 2
      decide
  realizes := by
    intro n right
    cases right
    all_goals
      change (Interactive.eval adaptiveCode
        (wholeInterface.bitOracle (countingOracle _))
        (Interactive.Configuration.initial 0 (wholeInterface.input n ())) 25).map
        Interactive.observe = (adaptive.run (countingOracle _) 0).map wholeInterface.encodeOutcome
      rw [adaptiveCode_run]
      first | rw [adaptive_left_run] | rw [adaptive_right_run]
      simp [PMF.pure_map, Interactive.observe, Interactive.Configuration.result,
        WholeInterface.encodeOutcome, wholeInterface, FiniteBitEncoding.bool]

/-- Full-time security quantifies over a genuinely inhabited machine class. -/
example : (wholeClass wholeInterface (fun _ => 25) (fun _ => 2)).admissible
    (fun _ => ()) (fun _ => adaptive) := ⟨adaptiveWholeWitness⟩

example : (wholeClass wholeInterface (fun _ => 100) (fun _ => 5)).admissible
    (fun _ => ()) (fun _ => adaptive) :=
  ⟨adaptiveWholeWitness.mono (fun _ => 100) (fun _ => 5)
    (fun _ => by decide) (fun _ => by decide)⟩

/-- The recorded number includes both call operations and all local transfer
and decision work; the native code alone has only four instructions. -/
example : adaptiveCode.length = 4 := rfl

noncomputable def wholeRelax : WholeReduction protocol protocol
    (Reduction.id (goal protocol)) wholeInterface wholeInterface
    (fun _ => 25) (fun _ => 2) (fun _ => 100) (fun _ => 5) where
  compiler := .identity
  mapWitness := fun _ _ W => W.mono (fun _ => 100) (fun _ => 5)
    (fun _ => by decide) (fun _ => by decide)
  code_eq := by intro F A W; rfl

example (ε : Nat → ℝ≥0∞)
    (h : WholeSecure wholeInterface (fun _ => 100) (fun _ => 5) (fun _ => ()) ε) :
    WholeSecure wholeInterface (fun _ => 25) (fun _ => 2) (fun _ => ()) ε :=
  (wholeRelax.comp (WholeReduction.id wholeInterface (fun _ => 100) (fun _ => 5))).secure
    (fun _ => ()) ε h

end CryptoOracle.Examples
