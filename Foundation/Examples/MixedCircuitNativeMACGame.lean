import Foundation.Examples.MixedCircuitNativeContinuation
import Foundation.Examples.RandomFunctionMACNativeOptimization

/-! The mixed native-segment evaluator realizes the original fixed MAC game,
including full oracle state, query history and success bit. The inherited
finite 1/256 bound is for the existing attack; no new asymptotic or arbitrary-
adversary bound is asserted. Key sampling and oracle internals remain external. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.NativeContinuation.Game
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Stateful
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

noncomputable def run {n m} (circuit : Circuit Clocked.signature n m) (input : Bundle Clocked.Values n) :
    PMF (Configuration MACNativeQuantitative.State) :=
  (uniform (Fin 8 → Fin 256)).bind fun key =>
    (Stateful.evaluate (nativeModel RandomFunctionMACNativeOptimized.code RandomOracle.Cube.coordinateOracle)
      circuit (Clocked.valid circuit) (MACNativeQuantitative.initial key) input).map Prod.fst

theorem run_eq {n m} (circuit : Circuit Clocked.signature n m)
    (duration : Clocked.ticks circuit = 286) (input : Bundle Clocked.Values n) :
    run circuit input = MACNativeQuantitative.run RandomFunctionMACNativeOptimized.code 286 := by
  unfold run MACNativeQuantitative.run
  congr 1
  funext key
  rw [continuing_frame, duration]

theorem full_law {n m} (circuit : Circuit Clocked.signature n m)
    (duration : Clocked.ticks circuit = 286) (input : Bundle Clocked.Values n) (order : Schedule 8) :
    (run circuit input).map RandomFunctionMACNativeCaller.Native.observe =
      CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw order := by
  rw [run_eq circuit duration]
  exact RandomFunctionMACNativeOptimization.full_law order

theorem forgery_bound {n m} (circuit : Circuit Clocked.signature n m)
    (duration : Clocked.ticks circuit = 286) (input : Bundle Clocked.Values n) (order : Schedule 8) :
    eventProb ((run circuit input).map RandomFunctionMACNativeCaller.Native.observe)
      (fun outcome => outcome.result = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [full_law circuit duration input order]
  exact CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.full_security order

end CryptoLogic.Polygraph.MixedCircuit.Examples.NativeContinuation.Game
