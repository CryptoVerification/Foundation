import Foundation.Examples.MixedCircuitMACNativeRepair
import Foundation.Examples.RandomFunctionMACNativeOptimization

/-! Concrete original/optimized native games with arbitrary nonempty mixed
MAC analysis. The native marginal retains the full physical frame and has the
existing 1/256 bound. Analysis boxes are not native opcodes and their cost is
not included in the caller's horizon. The attack and finite key space are fixed. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- This is the code emitted by the already certified optimizing compiler,
not a fresh abstract code selected only for the stochastic model. -/
theorem optimized_compiler_code (code : Code) :
    RandomFunctionMACNativeOptimization.optimized.compiler.run code = Implementation.optimized.code := rfl

theorem original_compiler_code (F A) (witness : RandomFunctionMACNativeOptimization.source.Witness F A) :
    RandomFunctionMACNativeOptimization.original.compiler.run witness.code = Implementation.original.code :=
  witness.executes.1

noncomputable def runGame (implementation : Implementation) (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (input : Outcome → Bundle (family orders) n) :
    PMF (Configuration MACNativeQuantitative.State × Bundle (family orders) m) :=
  (uniform (Fin 8 → Fin 256)).bind fun key =>
    run implementation orders circuit valid RandomOracle.Cube.coordinateOracle (Finset.univ, key) [] input

theorem runGame_native (implementation : Implementation) (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (input : Outcome → Bundle (family orders) n) :
    (runGame implementation orders circuit valid input).map Prod.fst =
      MACNativeQuantitative.run implementation.code implementation.horizon := by
  simp only [runGame, PMF.map_bind, run_state_marginal]
  rfl

theorem runGame_full_law (implementation : Implementation) (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (input : Outcome → Bundle (family orders) n) (order : Schedule 8) :
    ((runGame implementation orders circuit valid input).map Prod.fst).map RandomFunctionMACNativeCaller.Native.observe =
      CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.fullLaw order := by
  rw [runGame_native]
  cases implementation with
  | original => exact MACNativeQuantitative.native_full_law order
  | optimized => exact RandomFunctionMACNativeOptimization.full_law order

theorem runGame_security (implementation : Implementation) (orders : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (input : Outcome → Bundle (family orders) n) (order : Schedule 8) :
    eventProb (((runGame implementation orders circuit valid input).map Prod.fst).map RandomFunctionMACNativeCaller.Native.observe)
      (fun outcome => outcome.result = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [runGame_full_law implementation orders circuit valid input order]
  exact CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.full_security order

theorem runGame_refinement (orders : Nat → Schedule 8) {n m} (circuit : Circuit signature n m)
    (valid : Holds (MACNormalization.condition orders) circuit.needs) (input : Outcome → Bundle (family orders) n) :
    (runGame .original orders circuit valid input).map (Stateful.stateMap RandomFunctionMACNativeOptimized.relocate) =
      runGame .optimized orders circuit valid input := by
  simp only [runGame, PMF.map_bind]
  apply congrArg (fun continuation => (uniform (Fin 8 → Fin 256)).bind continuation)
  funext key
  exact run_refinement orders circuit valid RandomOracle.Cube.coordinateOracle (Finset.univ, key) [] input

/-- This example copies a real complete MAC outcome, analyzes both copies,
discards one analyzed result, and copies the retained analyzed result. It
never makes two native caller invocations or duplicates the physical state. -/
def analysis (stage : Nat) : Circuit signature (source (stage + 1)) (.pair finish finish) :=
  .seq (.wire (.copy (source (stage + 1))))
    (.seq (.tensor (before stage) (.seq (before stage) (.wire (.discard finish))))
      (.seq (.wire (.rightUnit finish)) (.wire (.copy finish))))

theorem analysis_needs (stage : Nat) : (analysis stage).needs = {stage} := by
  simp [analysis, before, Circuit.needs, signature, MACNormalization.layout]

theorem analysis_kernel (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (analysis stage).needs) (input : Outcome) :
    MixedCircuit.evaluate (MAC.base orders) (analysis stage) valid input =
      PMF.pure (MACNormalization.sanitize input, MACNormalization.sanitize input) := by
  simp only [analysis, MixedCircuit.evaluate, Wire.eval, before, base_schedule, base_eliminate,
    PMF.pure_bind, PMF.pure_map, append]

/-- The complete unsanitized native frame remains present beside the two
nonempty sanitized results of the mixed analysis. -/
theorem analysis_run (implementation : Implementation) (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (analysis stage).needs)
    (world : Oracle (Fin 8) (Fin 256) MACNativeQuantitative.State)
    (state : MACNativeQuantitative.State) (trace : List (List Bool × List Bool)) :
    run implementation orders (analysis stage) valid world state trace id =
      (frames implementation world state trace).map (fun frame =>
        (frame, (MACNormalization.sanitize (RandomFunctionMACNativeCaller.Native.observe frame),
          MACNormalization.sanitize (RandomFunctionMACNativeCaller.Native.observe frame)))) := by
  simp only [run, Stateful.evaluate_lift, analysis_kernel, PMF.pure_map, id_eq]
  rfl

theorem analysis_retains_state_trace (input : Outcome) :
    (MACNormalization.sanitize input).state = input.state ∧
      (MACNormalization.sanitize input).trace = input.trace := ⟨rfl, rfl⟩

/-- The existing native implementation bounds still apply to the physical
frame after this nonempty tensor/copy/discard analysis. -/
theorem analysis_terminal_queries (implementation : Implementation) (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (analysis stage).needs)
    (world : Oracle (Fin 8) (Fin 256) MACNativeQuantitative.State)
    (state : MACNativeQuantitative.State) (trace : List (List Bool × List Bool))
    (final : Configuration MACNativeQuantitative.State)
    (supported : final ∈ ((run implementation orders (analysis stage) valid world state trace id).map Prod.fst).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + 4 :=
  run_terminal_queries implementation orders (analysis stage) valid world state trace id final supported

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeContinuation
