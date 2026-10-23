import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulSimulation
import Foundation.Examples.MixedCircuitMAC
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeOptimizedRefinement

/-! One actual old/new native MAC execution followed by an arbitrary mixed
analysis diagram on its NONEMPTY complete outcome. The physical frame is kept
as the one threaded state. The diagram's proof boxes are analysis readouts,
not newly compiled native instructions; 343/286 bound the caller prefix only. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

inductive Implementation where
  | original | optimized

def Implementation.code : Implementation → Code
  | .original => RandomFunctionMACNativeCaller.Native.code
  | .optimized => RandomFunctionMACNativeOptimized.code

def Implementation.horizon : Implementation → Nat
  | .original => 343
  | .optimized => 286

noncomputable def frames {State : Type} (implementation : Implementation)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (trace : List (List Bool × List Bool)) :
    PMF (Configuration State) :=
  TimedExecution.eval (Reification.timedStep implementation.code (RandomFunctionMACNativeCaller.packetOracle world))
    implementation.horizon ⟨state, .running {}, trace⟩

theorem frames_refinement {State : Type} (world : Oracle (Fin 8) (Fin 256) State)
    (state : State) (trace : List (List Bool × List Bool)) :
    (frames .original world state trace).map RandomFunctionMACNativeOptimized.relocate =
      frames .optimized world state trace :=
  RandomFunctionMACNativeOptimized.whole_frame_refinement world state trace

noncomputable def run {State : Type} (implementation : Implementation) (orders : Nat → Schedule 8)
    {n m} (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (trace : List (List Bool × List Bool))
    (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n) : PMF (Configuration State × Bundle (family orders) m) :=
  (frames implementation world state trace).bind fun frame =>
    Stateful.evaluate (Stateful.lift (MAC.base orders)) circuit valid frame
      (input (RandomFunctionMACNativeCaller.Native.observe frame))

/-- Every mixed circuit, including copy/drop of sampled full outcomes, is
compatible with the concrete full-frame old/new native correspondence. -/
theorem run_refinement {State : Type} (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (trace : List (List Bool × List Bool))
    (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n) :
    (run .original orders circuit valid world state trace input).map
      (Stateful.stateMap RandomFunctionMACNativeOptimized.relocate) =
    run .optimized orders circuit valid world state trace input := by
  simp only [run, PMF.map_bind]
  rw [← frames_refinement world state trace, PMF.bind_map]
  apply congrArg (fun continuation => (frames .original world state trace).bind continuation)
  funext frame
  simp only [Function.comp_def, RandomFunctionMACNativeOptimized.observe_relocate]
  exact (Stateful.lift_simulation (MAC.base orders) RandomFunctionMACNativeOptimized.relocate).evaluate
    circuit valid frame (input (RandomFunctionMACNativeCaller.Native.observe frame))

/-- Arbitrary correlation between earlier history, oracle state and the
existing bit transcript survives the representation change. -/
theorem run_refinement_joint {State Context : Type} (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle (Fin 8) (Fin 256) State) (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n)
    (law : PMF (Context × (State × List (List Bool × List Bool)))) :
    law.bind (fun past => (run .original orders circuit valid world past.2.1 past.2.2 input).map
      (fun result => (past, Stateful.stateMap RandomFunctionMACNativeOptimized.relocate result))) =
    law.bind (fun past => (run .optimized orders circuit valid world past.2.1 past.2.2 input).map
      (fun result => (past, result))) := by
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  have same := congrArg (PMF.map (fun result => (past, result)))
    (run_refinement orders circuit valid world past.2.1 past.2.2 input)
  simpa only [PMF.map_comp, Function.comp_def] using same

/-- Analysis cannot erase the original physical tapes, state or transcript,
even when all of its output ports are discarded. -/
theorem run_state_marginal {State : Type} (implementation : Implementation) (orders : Nat → Schedule 8)
    {n m} (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (trace : List (List Bool × List Bool))
    (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n) :
    (run implementation orders circuit valid world state trace input).map Prod.fst =
      frames implementation world state trace := by
  simp only [run, PMF.map_bind, Stateful.lift_state_marginal, PMF.bind_pure]

theorem run_terminal_queries {State : Type} (implementation : Implementation) (orders : Nat → Schedule 8)
    {n m} (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (trace : List (List Bool × List Bool))
    (input : CryptoOracle.Outcome (Fin 8) (Fin 256) Bool State → Bundle (family orders) n) (final : Configuration State)
    (supported : final ∈ ((run implementation orders circuit valid world state trace input).map Prod.fst).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [run_state_marginal] at supported
  cases implementation with
  | original => exact RandomFunctionMACNativeCaller.Native.whole_halts_queries world state trace final supported
  | optimized => exact RandomFunctionMACNativeOptimized.whole_halts_queries world state trace final supported


/-- Request format is checked before the native oracle service runs. The
analysis diagram does not create additional physical oracle requests. -/
theorem prefix_awaiting_format {State : Type} (implementation : Implementation)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (fuel : Nat)
    (within : fuel ≤ implementation.horizon) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval
      (Reification.timedStep implementation.code (RandomFunctionMACNativeCaller.packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support)
    (machine : Machine.Configuration) (request : List Bool) (waiting : current.control = .awaiting machine request) :
    ∃ message : Fin 8, request = RandomFunctionMACNativeCaller.encodeMessage message := by
  cases implementation with
  | original => exact RandomFunctionMACNativeCaller.Native.awaiting_format world state fuel within current supported machine request waiting
  | optimized => exact RandomFunctionMACNativeOptimized.awaiting_format world state fuel within current supported machine request waiting

theorem prefix_transcript_encoded {State : Type} (implementation : Implementation)
    (world : Oracle (Fin 8) (Fin 256) State) (state : State) (fuel : Nat)
    (within : fuel ≤ implementation.horizon) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval
      (Reification.timedStep implementation.code (RandomFunctionMACNativeCaller.packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support) :
    ∀ entry ∈ current.reverseTrace, ∃ message : Fin 8, ∃ tag : Fin 256,
      entry = (RandomFunctionMACNativeCaller.encodeMessage message, RandomFunctionMACNativeCaller.encodeTag tag) := by
  cases implementation with
  | original => exact RandomFunctionMACNativeCaller.Native.prefix_encoded world state fuel within current supported
  | optimized => exact RandomFunctionMACNativeOptimized.prefix_encoded world state fuel within current supported

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
