import Foundation.Constructions.Symmetric.SecretPrefixMACPublicCompression
import Foundation.Constructions.Hash.Chains

/-! Merge the fixed compression simulator into a ROM MAC attacker using the
existing stateful inliner. Private table inspection never receives the key or
the opaque RO state. Simulator-local uniform tags become existing fair coins. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Internal simulator hash requests become public MAC hash requests.
Uniform n-bit outputs use n local fair coins and zero oracle calls. -/
def simulatorROMHandler {κ n : Nat} : Foundation.Hash.SimulatorRequest (Bits κ) →
    Program (Request κ) (Tag n) (Tag n)
  | .inl message => .query (.inl message) Program.done
  | .inr () => Program.sampleBitsWith n Program.done

def mergeProcedure {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n)) :
    PublicRequest κ n → Program (Request κ) (Tag n) (Foundation.Hash.CompressionTable (Bits κ) (Bits n) × Tag n)
  | .inl request => .query request (fun response => .done (table, response))
  | .inr compression => Program.inline simulatorROMHandler
      (Foundation.Hash.simulatorProgram initial terminal table compression)

def mergeAttack {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n)) (attack : PublicAttack κ n) : Attack κ n :=
  (Program.inlineState (mergeProcedure initial terminal) table attack).bind (fun pair => .done pair.2)

/-- The simulator compiler keeps the signed list, and shares exactly the
original MAC hash state. It does not count a local draw as a hash request. -/
theorem simulatorROMHandler_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (state : State) (signed : List (Message κ)) (request : Foundation.Hash.SimulatorRequest (Bits κ)) :
    ((simulatorROMHandler request).run (oracle hash key) (state, signed)).map Program.resultState =
      (Foundation.Hash.simulatorBackend hash state request).map (fun answer => ((answer.1, signed), answer.2)) := by
  cases request with
  | inl message =>
      simp only [simulatorROMHandler, Program.run, oracle, PMF.map_bind, PMF.bind_map,
        PMF.pure_map, Program.resultState, Foundation.Hash.simulatorBackend, Function.comp_def]
      rfl
  | inr value =>
      cases value
      simp only [simulatorROMHandler, Program.sampleBitsWith_run, Program.run, PMF.map_bind,
        PMF.pure_map, Program.resultState, Foundation.Hash.simulatorBackend, PMF.map_comp, Function.comp_def]
      rfl

/-- Actual simulator execution, including its private state and output,
is preserved by the fair-coin compiler on the original MAC oracle. -/
theorem compiledSimulator_run {κ n : Nat} {State Result : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (state : State) (signed : List (Message κ))
    (program : Program (Foundation.Hash.SimulatorRequest (Bits κ)) (Tag n) Result) :
    ((Program.inline simulatorROMHandler program).run (oracle hash key) (state, signed)).map Program.resultState =
      (program.run (Foundation.Hash.simulatorBackend hash) state).map
        (fun out => ((out.state, signed), out.result)) := by
  rw [Program.inline_run]
  have lifted := Program.run_state_map (fun st : State => (st, signed))
    (Foundation.Hash.simulatorBackend hash)
    (Program.implementedOracle simulatorROMHandler (oracle hash key))
    (by intro st request; exact (simulatorROMHandler_run hash key st signed request).symm)
    program state
  have result := congrArg (PMF.map Program.resultState) lifted
  simpa only [PMF.map_comp, Program.mapState, Program.resultState, Function.comp_def] using result.symm

/-- Reassociation of private simulator state, RO state and signed messages
is the only state conversion needed for the three public windows. -/
def mergeState {κ n : Nat} {State : Type}
    (state : Foundation.Hash.CompressionTable (Bits κ) (Bits n) × (State × List (Message κ))) :
    (Foundation.Hash.CompressionTable (Bits κ) (Bits n) × State) × List (Message κ) :=
  ((state.1, state.2.1), state.2.2)

theorem mergeProcedure_step {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ) (initial : Bits n) (terminal : Bits κ)
    (state : Foundation.Hash.CompressionTable (Bits κ) (Bits n) × (State × List (Message κ)))
    (request : PublicRequest κ n) :
    (Program.statefulOracle (mergeProcedure initial terminal) (oracle hash key) state request).map
      (fun answer => (mergeState answer.1, answer.2)) =
      publicOracle ((Foundation.Hash.candidate initial terminal).world hash) key (mergeState state) request := by
  cases request with
  | inl request =>
      cases request <;>
        simp [Program.statefulOracle, mergeProcedure, Program.run, oracle, publicOracle, mergeState,
          Foundation.Hash.Simulator.world, PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def, tag] <;> rfl
  | inr compression =>
      have result := congrArg (PMF.map (fun pair : (State × List (Message κ)) ×
          (Foundation.Hash.CompressionTable (Bits κ) (Bits n) × Tag n) =>
        (((pair.2.1, pair.1.1), pair.1.2), pair.2.2)))
        (compiledSimulator_run hash key state.2.1 state.2.2
          (Foundation.Hash.simulatorProgram initial terminal state.1 compression))
      simpa only [Program.statefulOracle, mergeProcedure, mergeState, publicOracle,
        Foundation.Hash.candidate, Foundation.Hash.Simulator.world, Foundation.Hash.compressionSimulator,
        PMF.map_comp, Program.resultState, Function.comp_def] using result

/-- Exact joint final hash-state, signed-list and forgery law. The public
compression trace and compiled ROM trace use different query units. -/
theorem mergeAttack_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ) (initial : Bits n) (terminal : Bits κ)
    (state : State) (signed : List (Message κ))
    (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n)) (attack : PublicAttack κ n) :
    ((mergeAttack initial terminal table attack).run (oracle hash key) (state, signed)).map Program.resultState =
      (attack.run (publicOracle ((Foundation.Hash.candidate initial terminal).world hash) key)
        ((table, state), signed)).map (fun out => ((out.state.1.2, out.state.2), out.result)) := by
  have projected := Program.run_state_map mergeState
    (Program.statefulOracle (mergeProcedure initial terminal) (oracle hash key))
    (publicOracle ((Foundation.Hash.candidate initial terminal).world hash) key)
    (mergeProcedure_step hash key initial terminal) attack (table, (state, signed))
  have compiled := Program.inlineState_run (mergeProcedure initial terminal) attack (oracle hash key)
    table (state, signed)
  have observed := congrArg (PMF.map (fun out => ((out.state.1.2, out.state.2), out.result))) projected
  simp only [PMF.map_comp, Program.mapState, mergeState, Function.comp_def] at observed
  have discarded := congrArg (PMF.map (fun pair => (pair.1, pair.2.2))) compiled
  simp only [PMF.map_comp, Program.resultState, Function.comp_def] at discarded
  simp only [mergeAttack, Program.run_bind, PMF.map_bind, Program.run, PMF.pure_map, Program.resultState]
  exact discarded.trans observed

/-- Merging the simulator produces an ordinary ROM MAC attacker with exactly
the same success law. The same hash state is used for every simulated request
and for the final verification, with no resetting or second attack stage. -/
theorem mergeAttack_game {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (initial : Bits n) (terminal : Bits κ)
    (state : State) (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n))
    (messageLimit : Nat) (attack : PublicAttack κ n) :
    game hash state messageLimit (mergeAttack initial terminal table attack) =
      publicGame ((Foundation.Hash.candidate initial terminal).world hash) (table, state) messageLimit attack := by
  unfold game publicGame
  congr 1
  funext key
  have result := congrArg (fun law => law.bind (fun pair =>
    (verify hash key pair.1.1 pair.2.1 pair.2.2).map (fun answer =>
      answer.2 && decide (pair.2.1 ∉ pair.1.2) && decide (pair.2.1.length ≤ messageLimit))))
    (mergeAttack_run hash key initial terminal state [] table attack)
  simp only [PMF.bind_map, Program.resultState, Function.comp_def] at result
  rw [result]
  congr 1
  funext out
  simp only [verify, tag, Program.adaptOracle, Foundation.Hash.Simulator.world,
    PMF.map_comp, Function.comp_def, id_eq]

end Foundation.Symmetric.SecretPrefixMAC
