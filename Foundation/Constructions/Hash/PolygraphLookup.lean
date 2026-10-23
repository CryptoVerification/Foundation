import Foundation.Crypto.Logic.Polygraph.RandomOracle
import Foundation.Constructions.Hash.NativeSimulatorLookup

/-! Connect the coherent random-oracle witness to the existing native table
lookup. These are actual bit-machine transitions, with the caller's table and
query already encoded. Initialization, insertion and fresh sampling are not
included in this lookup component's budget. No dense random table is executed. -/
namespace Foundation.Hash.Native.SimulatorLookup.Polygraph

open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability
open Foundation.Symmetric
open CryptoOracle.RandomOracle
set_option backward.isDefEq.respectTransparency false

variable {n κ : Nat} {State Result : Type}

abbrev Key (n κ : Nat) := CompressionInput (Bits κ) (Bits n)

/-- Precisely the public response packet, with the external state and prior
trace. The physical table layout remains in the machine's input tape. -/
def observe (frame : Configuration State) :
    State × List (List Bool × List Bool) × Option Tape :=
  (frame.state, frame.reverseTrace,
    match frame.control with | .running machine => some machine.outputTape | _ => none)

/-- A concrete adaptive lazy-oracle outcome is linked to the very same cube
assignment used by the proof. Native lookup reads that outcome's actual list. -/
theorem coupled_lookup (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (pair : Outcome (Key n κ) (Bits n) Result (CompressionTable (Bits κ) (Bits n)) ×
      (Finset (Key n κ) → (Cube.cube (Key n κ) (Bits n)).State))
    (hp : pair ∈ (Cube.coupled program).support)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : Key n κ) (beforeInput beforeOutput : List (Option Bool)) :
    (TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (lookupSteps query pair.1.state)
      (NativeCode.frame state trace (scanStart pair.1.state query beforeInput beforeOutput))).map
        observe = PMF.pure (state, trace, some
          ({ left := (lookupResponse (Cube.view (pair.2 (Cube.seen pair.1.state)) query)).reverse.map some ++
            (compressionPacket query).reverse.map some ++ beforeOutput } : Tape)) := by
  rw [lookup_run, PMF.pure_map]
  simp only [observe, NativeCode.frame, lookupFinish_output]
  rw [Cube.coupled_cache program pair hp query]
  simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq]

/-- The first actual halt retains the response and its exact transition
count in one joint distribution. This is not a declared host-function cost. -/
theorem coupled_lookup_first (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (pair : Outcome (Key n κ) (Bits n) Result (CompressionTable (Bits κ) (Bits n)) ×
      (Finset (Key n κ) → (Cube.cube (Key n κ) (Bits n)).State))
    (hp : pair ∈ (Cube.coupled program).support)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : Key n κ) (beforeInput beforeOutput : List (Option Bool)) :
    (TimedExecution.runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (fun frame => Reification.terminal frame.control) (lookupSteps query pair.1.state)
      (NativeCode.frame state trace (scanStart pair.1.state query beforeInput beforeOutput))).map
        (fun result => (observe result.1, result.2)) =
      PMF.pure ((state, trace, some
        ({ left := (lookupResponse (Cube.view (pair.2 (Cube.seen pair.1.state)) query)).reverse.map some ++
          (compressionPacket query).reverse.map some ++ beforeOutput } : Tape)),
        lookupSteps query pair.1.state) := by
  rw [lookup_first_joint, PMF.pure_map]
  simp only [observe, NativeCode.frame, lookupFinish_output]
  rw [Cube.coupled_cache program pair hp query]
  simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq]

/-- A query-bounded adaptive client leaves at most q entries in this actual
lazy table. All comparisons, movements, response copying and halt of lookup
are counted by the existing native execution theorem. -/
theorem coupled_lookup_budget {program : CryptoOracle.Program (Key n κ) (Bits n) Result}
    {q : Nat} (hq : program.BoundedQueries q)
    (pair : Outcome (Key n κ) (Bits n) Result (CompressionTable (Bits κ) (Bits n)) ×
      (Finset (Key n κ) → (Cube.cube (Key n κ) (Bits n)).State))
    (hp : pair ∈ (Cube.coupled program).support) (query : Key n κ) :
    lookupSteps query pair.1.state ≤ q * (9 * n + 8 * κ + 18) + 12 * n + 7 * κ + 19 := by
  have hlazy : pair.1 ∈ (program.run RandomOracle.oracle []).support := by
    rw [← Cube.coupled_lazy program]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, hp, rfl⟩
  have hsize : pair.1.state.length ≤ q := by
    simpa using RandomOracle.bounded_table hq [] pair.1 hlazy
  calc
    _ ≤ lookupBudget n κ pair.1.state.length := lookupSteps_le query pair.1.state
    _ ≤ _ := by
      rw [lookupBudget_eq]
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_right (9 * n + 8 * κ + 18) hsize) (12 * n)) (7 * κ)) 19

end Foundation.Hash.Native.SimulatorLookup.Polygraph
