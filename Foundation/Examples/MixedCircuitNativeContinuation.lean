import Foundation.Crypto.Logic.Polygraph.MixedCircuitClocked
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeOptimizedRefinement

/-! A concrete use of mixed tensor/copy/discard to schedule segments of the
existing native MAC caller without restarting it. All segments use the same
native program and external oracle; this is not the full mixed cryptographic
rewrite presentation nor execution of different programs in parallel. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.NativeContinuation
open Foundation.Probability
open Foundation.Symmetric
open CryptoOracle CryptoOracle.Interactive
open Stateful
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

noncomputable def nativeModel {State : Type} (code : Code) (world : Oracle (Fin 8) (Fin 256) State) :=
  Clocked.model (Reification.timedStep code (RandomFunctionMACNativeCaller.packetOracle world))

theorem continuing_frame {State : Type} (code : Code) (world : Oracle (Fin 8) (Fin 256) State)
    {n m} (circuit : Circuit Clocked.signature n m)
    (proof : CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Holds (fun _ => True) circuit.needs)
    (frame : Configuration State) (input : Bundle Clocked.Values n) :
    (Stateful.evaluate (nativeModel code world) circuit proof frame input).map Prod.fst =
      TimedExecution.eval (Reification.timedStep code (RandomFunctionMACNativeCaller.packetOracle world))
        (Clocked.ticks circuit) frame :=
  Clocked.state_marginal _ circuit proof frame input

/-- Every mixed schedule of the optimized caller with total 286 transitions
inherits the actual universal stopping and four-call theorem. -/
theorem optimized_halts_queries {State : Type} (world : Oracle (Fin 8) (Fin 256) State)
    {n m} (circuit : Circuit Clocked.signature n m) (duration : Clocked.ticks circuit = 286)
    (state : State) (trace : List (List Bool × List Bool)) (input : Bundle Clocked.Values n)
    (final : Configuration State)
    (supported : final ∈ ((Stateful.evaluate (nativeModel RandomFunctionMACNativeOptimized.code world)
      circuit (Clocked.valid circuit) ⟨state, .running {}, trace⟩ input).map Prod.fst).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 := by
  rw [continuing_frame, duration] at supported
  exact RandomFunctionMACNativeOptimized.whole_halts_queries world state trace final supported

theorem optimized_observation {State : Type} (world : Oracle (Fin 8) (Fin 256) State)
    {n m} (circuit : Circuit Clocked.signature n m) (duration : Clocked.ticks circuit = 286)
    (state : State) (input : Bundle Clocked.Values n) :
    ((Stateful.evaluate (nativeModel RandomFunctionMACNativeOptimized.code world) circuit (Clocked.valid circuit)
      ⟨state, .running {}, []⟩ input).map Prod.fst).map RandomFunctionMACNativeCaller.Native.observe =
      RandomFunctionMACNativeCaller.target.run world state := by
  rw [continuing_frame, duration]
  exact RandomFunctionMACNativeOptimized.observation_law world state

/-- The old-to-new complete-frame correspondence remains valid for any two
mixed schedules with their respective verified budgets. -/
theorem refinement {State : Type} (world : Oracle (Fin 8) (Fin 256) State)
    {n m n' m'} (old : Circuit Clocked.signature n m) (updated : Circuit Clocked.signature n' m')
    (oldDuration : Clocked.ticks old = 343) (newDuration : Clocked.ticks updated = 286)
    (state : State) (trace : List (List Bool × List Bool))
    (input : Bundle Clocked.Values n) (input' : Bundle Clocked.Values n') :
    ((Stateful.evaluate (nativeModel RandomFunctionMACNativeCaller.Native.code world) old (Clocked.valid old)
      ⟨state, .running {}, trace⟩ input).map Prod.fst).map RandomFunctionMACNativeOptimized.relocate =
    (Stateful.evaluate (nativeModel RandomFunctionMACNativeOptimized.code world) updated (Clocked.valid updated)
      ⟨state, .running {}, trace⟩ input').map Prod.fst := by
  rw [continuing_frame, continuing_frame, oldDuration, newDuration]
  exact RandomFunctionMACNativeOptimized.whole_frame_refinement world state trace

/-- Concrete split: copy only the empty port, execute 100 and then 186 native
transitions with one frame, discard only the resulting empty port pair. -/
def split : Circuit Clocked.signature .unit .unit :=
  .seq (.wire (.copy .unit))
    (.seq (.tensor (.box 100) (.box 186)) (.wire (.discard _)))

theorem split_ticks : Clocked.ticks split = 286 := by decide_cbv

theorem split_full_frame {State : Type} (world : Oracle (Fin 8) (Fin 256) State) (frame : Configuration State) :
    (Stateful.evaluate (nativeModel RandomFunctionMACNativeOptimized.code world) split (Clocked.valid split)
      frame PUnit.unit).map Prod.fst =
    TimedExecution.eval (Reification.timedStep RandomFunctionMACNativeOptimized.code
      (RandomFunctionMACNativeCaller.packetOracle world)) 286 frame := by
  rw [continuing_frame, split_ticks]

end CryptoLogic.Polygraph.MixedCircuit.Examples.NativeContinuation
