import Foundation.Crypto.Semantics.Oracle.InteractiveMachine
import Foundation.Crypto.Semantics.Machine.PolynomialTime

/-! One fixed finite code performs a public unary-bounded number of adaptive
Boolean oracle calls. Replies become the next requests. The caller's bound
is data on the input tape, never a security-parameter-dependent code family. -/
namespace CryptoOracle.CountedLoop

open Foundation.Probability Machine Interactive
universe u
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- Initial request false; the unary input determines the number of calls.
def code : Interactive.Code :=
  [.native (.write .output false), .native (.moveRight .output), .native (.moveLeft .output),
   .native (.branch .input 7 7 4), .native (.moveRight .input), .call,
   .native (.jump 3), .native .halt]

abbrev BoolOracle (State : Type u) := State → Bool → ProbComp (State × Bool)

noncomputable def bitOracle {State : Type u} (oracle : BoolOracle State) : BitOracle State :=
  fun state request => (oracle state (request.headD false)).map fun (state', bit) => (state', [bit])

def loopConfig {State : Type u} (state : State) (remaining : Nat) (past : List (Option Bool))
    (bit : Bool) (trace : List (List Bool × List Bool)) : Configuration State :=
  ⟨state, .running { pc := 3, inputTape := { (Tape.ofBits (List.replicate remaining true)) with left := past }, outputTape := { current := some bit, right := [none] } }, trace⟩

/-- General semigroup law for bounded operational execution. -/
theorem eval_add {State : Type u} (program : Interactive.Code) (oracle : BitOracle State)
    (start : Configuration State) (fuel extra : Nat) :
    Interactive.eval program oracle start (fuel + extra) =
      (Interactive.eval program oracle start fuel).bind fun c => Interactive.eval program oracle c extra := by
  induction extra with
  | zero => simp [Interactive.eval]
  | succ extra ih =>
      rw [Nat.add_succ, Interactive.eval, ih, PMF.bind_bind]
      rfl

/-- Branch, one input-head move, all request/response transfer cells and
one jump cost fourteen transitions, independently of oracle responses. -/
theorem iteration {State : Type u} (oracle : BoolOracle State) (state : State)
    (remaining : Nat) (past : List (Option Bool)) (bit : Bool)
    (trace : List (List Bool × List Bool)) :
    Interactive.eval code (bitOracle oracle) (loopConfig state (remaining + 1) past bit trace) 14 =
      (oracle state bit).map fun response =>
        loopConfig response.1 remaining (some true :: past) response.2
          (([bit], [response.2]) :: trace) := by
  cases remaining <;> cases bit <;>
    simp [Interactive.eval, Interactive.step, Interactive.transition, code, loopConfig, bitOracle,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Tape.ofBits, Tape.write, Tape.moveRight, Tape.moveLeft,
      List.replicate_succ, PMF.bind_map, PMF.map_comp, Function.comp_def] <;> rfl

/-- The final branch, halt, and result dispatch are all charged. -/
theorem finish {State : Type u} (oracle : BoolOracle State) (state : State)
    (past : List (Option Bool)) (bit : Bool) (trace : List (List Bool × List Bool)) :
    Interactive.eval code (bitOracle oracle) (loopConfig state 0 past bit trace) 3 =
      PMF.pure (⟨state, .finished bit, trace⟩ : Configuration State) := by
  simp [Interactive.eval, Interactive.step, Interactive.transition, code, loopConfig,
    Machine.Instruction.next, Machine.Configuration.tape, Tape.ofBits]

/-- Analysis-only adaptive law, preserving the full state and reverse trace. -/
noncomputable def law {State : Type u} (oracle : BoolOracle State) :
    Nat → State → Bool → List (List Bool × List Bool) → ProbComp (Configuration State)
  | 0, state, bit, trace => PMF.pure ⟨state, .finished bit, trace⟩
  | q + 1, state, bit, trace => (oracle state bit).bind fun response =>
      law oracle q response.1 response.2 (([bit], [response.2]) :: trace)

theorem run_loop {State : Type u} (oracle : BoolOracle State) (state : State) (count : Nat)
    (past : List (Option Bool)) (bit : Bool) (trace : List (List Bool × List Bool)) :
    Interactive.eval code (bitOracle oracle) (loopConfig state count past bit trace) (14 * count + 3) =
      law oracle count state bit trace := by
  induction count generalizing state past bit trace with
  | zero => exact finish _ _ _ _ _
  | succ count ih =>
      have ht : 14 * (count + 1) + 3 = 14 + (14 * count + 3) := by omega
      rw [ht, eval_add, iteration, PMF.bind_map]
      change (oracle state bit).bind _ = _
      congr 1
      funext response
      exact ih _ _ _ _

theorem prepare {State : Type u} (oracle : BoolOracle State) (state : State) (count : Nat) :
    Interactive.eval code (bitOracle oracle)
      (Configuration.initial state (List.replicate count true)) 3 =
    PMF.pure (loopConfig state count [] false []) := by
  cases count <;> simp [Interactive.eval, Interactive.step, Interactive.transition, code, loopConfig,
    Interactive.Configuration.initial, Machine.Configuration.initial, Machine.Instruction.next,
    Machine.Configuration.updateTape, Machine.Configuration.advance,
    Tape.write, Tape.moveRight, Tape.moveLeft, Tape.ofBits, List.replicate_succ]

theorem run {State : Type u} (oracle : BoolOracle State) (state : State) (count : Nat) :
    Interactive.eval code (bitOracle oracle)
      (Configuration.initial state (List.replicate count true)) (14 * count + 6) =
    law oracle count state false [] := by
  have ht : 14 * count + 6 = 3 + (14 * count + 3) := by omega
  rw [ht, eval_add, prepare, PMF.pure_bind, run_loop]

theorem law_support {State : Type u} (oracle : BoolOracle State) (count : Nat)
    (state : State) (bit : Bool) (trace : List (List Bool × List Bool))
    (out : Configuration State) (h : out ∈ (law oracle count state bit trace).support) :
    out.complete ∧ out.reverseTrace.length = count + trace.length := by
  induction count generalizing state bit trace out with
  | zero =>
      simp only [law, PMF.mem_support_pure_iff] at h
      subst out
      exact ⟨⟨bit, rfl⟩, by simp⟩
  | succ count ih =>
      rw [law, PMF.mem_support_bind_iff] at h
      obtain ⟨response, _, h⟩ := h
      have ht := ih response.1 response.2 (([bit], [response.2]) :: trace) out h
      refine ⟨ht.1, ?_⟩
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.2

theorem halts {State : Type u} (oracle : BoolOracle State) (state : State) (count : Nat) :
    Interactive.HaltsWithin code (bitOracle oracle)
      (Configuration.initial state (List.replicate count true)) (14 * count + 6) := by
  intro out h
  rw [run] at h
  exact (law_support oracle count state false [] out h).1

theorem queries {State : Type u} (oracle : BoolOracle State) (state : State) (count : Nat)
    (out : Configuration State)
    (h : out ∈ (Interactive.eval code (bitOracle oracle)
      (Configuration.initial state (List.replicate count true)) (14 * count + 6)).support) :
    out.reverseTrace.length = count := by
  rw [run] at h
  simpa only [List.length_nil, Nat.add_zero] using (law_support oracle count state false [] out h).2

/-- A security-parameter-dependent query bound changes only the input tape.
The same eight-instruction code is used at every parameter. -/
theorem profile_halts {State : Type u} (oracle : BoolOracle State) (state : Nat → State)
    (q : Nat → Nat) (n : Nat) :
    Interactive.HaltsWithin code (bitOracle oracle)
      (Configuration.initial (state n) (List.replicate (q n) true)) (14 * q n + 6) := halts _ _ _

theorem profile_time_polynomial {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (fun n => 14 * q n + 6) :=
  ((PolynomiallyBounded.const 14).mul hq).add (PolynomiallyBounded.const 6)

end CryptoOracle.CountedLoop
