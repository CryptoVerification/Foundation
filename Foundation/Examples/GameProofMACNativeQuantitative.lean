import Foundation.Crypto.Logic.Polygraph.GameProofQuantitative
import Foundation.Crypto.Logic.General.QuantitativeObservation
import Foundation.Crypto.Logic.General.Backends
import Foundation.Examples.GameProofMACNormalization
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCorrectness

/-! Concrete native certificates for the original adaptive MAC proof boxes.
Preparation changes are proof changes; the 251-instruction caller still runs
once, with four calls, within 343 transitions. The typed oracle remains an
external capability. Sanitization is an analysis readout, not a new opcode;
the unsanitized complete native observation is retained independently. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNativeQuantitative
open Foundation.Probability Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.General
open Foundation.Symmetric
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
abbrev State := Finset (Fin 8) × (Fin 8 → Fin 256)
abbrev FullOutcome := GameCoherence.Examples.MAC.FullOutcome

def initial (key : Fin 8 → Fin 256) : Configuration State := ⟨(Finset.univ, key), .running {}, []⟩

noncomputable def run (code : Code) (horizon : Nat) : PMF (Configuration State) :=
  (uniform (Fin 8 → Fin 256)).bind fun key =>
    TimedExecution.eval (Reification.timedStep code (Foundation.Symmetric.RandomFunctionMACNativeCaller.packetOracle CryptoOracle.RandomOracle.Cube.coordinateOracle)) horizon
      (initial key)

def ExecutionContract (code : Code) (horizon : Nat) : Prop :=
  code = Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.code ∧ horizon = 343 ∧
  ∀ key : Fin 8 → Fin 256,
    Reification.HaltsWithin code (Foundation.Symmetric.RandomFunctionMACNativeCaller.packetOracle CryptoOracle.RandomOracle.Cube.coordinateOracle)
      (initial key) horizon ∧
    ∀ final ∈ (TimedExecution.eval (Reification.timedStep code (Foundation.Symmetric.RandomFunctionMACNativeCaller.packetOracle CryptoOracle.RandomOracle.Cube.coordinateOracle)) horizon
      (initial key)).support,
      Reification.terminal final.control = true ∧ final.reverseTrace.length = 4

theorem caller_contract : ExecutionContract Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.code 343 := by
  refine ⟨rfl, rfl, fun key => ⟨Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.haltsWithin CryptoOracle.RandomOracle.Cube.coordinateOracle (Finset.univ, key) [], ?_⟩⟩
  intro final supported
  simpa only [List.length_nil, Nat.zero_add] using
    Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.whole_halts_queries CryptoOracle.RandomOracle.Cube.coordinateOracle (Finset.univ, key) [] final supported

theorem native_full_law (order : Schedule 8) :
    (run Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.code 343).map Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observe = GameCoherence.Examples.MAC.fullLaw order := by
  unfold run GameCoherence.Examples.MAC.fullLaw
  simp_rw [RandomFunctionMACSchedules.scheduled_state, CryptoOracle.RandomOracle.Cube.query_eq, Finset.empty_union]
  rw [PMF.map_bind]
  apply congrArg (fun continuation => (uniform (Fin 8 → Fin 256)).bind continuation)
  funext key
  simpa only [initial, Foundation.Symmetric.RandomFunctionMACNativeCaller.target_eq_checked] using
    Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observation_law
      CryptoOracle.RandomOracle.Cube.coordinateOracle (Finset.univ, key)


def NativeRealizes (code : Code) (horizon : Nat) : Prop := ∀ order : Schedule 8,
  (run code horizon).map Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observe =
    GameCoherence.Examples.MAC.fullLaw order

def rawGoal : CryptoGoal where
  Instance _ := Unit
  Adversary _ _ := Unit
  advantage _ _ _ := 0

noncomputable def rawObject : General.SecurityObject.{0, 0} General.Backends.system .interactive where
  goal := rawGoal
  execution := {
    Resources := Nat
    ExecutesWithin := fun _ => ExecutionContract
    Realizes := fun _ _ => NativeRealizes }
  adversaries := ⟨fun _ _ => True⟩
  represented := by
    intro F A admissible
    exact ⟨Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.code, 343, caller_contract, native_full_law⟩

noncomputable def observation (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex) :
    Experiment.Observation rawObject := fun _ _ _ => match vertex with
  | .stage n => (GameCoherence.Examples.MAC.fullGame (orders n)).probability
  | .finish => 0

noncomputable def object (orders : Nat → Schedule 8) (vertex : MACNormalization.Vertex) :=
  Experiment.observe rawObject (observation orders vertex)

noncomputable def statisticalLoss : AdvantageBound where
  eval _ epsilon := epsilon + (256 : ℝ≥0∞)⁻¹
  monotone _ _ _ bound := add_le_add bound (le_refl _)

noncomputable def schedule (orders : Nat → Schedule 8) (stage : Nat) :
    General.QuantitativeReduction (object orders (.stage (stage + 1))) (object orders (.stage stage)) :=
  General.QuantitativeReduction.observe rawObject
    (observation orders (.stage (stage + 1))) (observation orders (.stage stage)) AdvantageBound.id (by
      intro n input observer
      change (GameCoherence.Examples.MAC.fullGame (orders (stage + 1))).probability ≤
        (GameCoherence.Examples.MAC.fullGame (orders stage)).probability
      exact (congrArg (fun law : PMF FullOutcome => eventProb law (fun out => out.result = true))
        (GameCoherence.Examples.MAC.full_law_eq (orders (stage + 1)) (orders stage))).le)

noncomputable def eliminate (orders : Nat → Schedule 8) (stage : Nat)
    (secure : MACNormalization.condition orders stage) :
    General.QuantitativeReduction (object orders (.stage stage)) (object orders .finish) :=
  General.QuantitativeReduction.observe rawObject
    (observation orders (.stage stage)) (observation orders .finish) statisticalLoss (by
      intro n input observer
      change (GameCoherence.Examples.MAC.fullGame (orders stage)).probability ≤ 0 + (256 : ℝ≥0∞)⁻¹
      simpa only [zero_add, MACNormalization.condition] using secure)

noncomputable def base (orders : Nat → Schedule 8) :
    Quantitative.Model General.Backends.system MACNormalization.layout (MACNormalization.condition orders) where
  machine _ := .interactive
  object := object orders
  atom label valid := match label with
    | .schedule stage => schedule orders stage
    | .eliminate stage => eliminate orders stage (valid stage (by simp [MACNormalization.layout]))

noncomputable def model (orders : Nat → Schedule 8) :
    Quantitative.HigherModel General.Backends.system MACNormalization.layout MACNormalization.relators
      (MACNormalization.condition orders) where
  base := base orders
  comparison := by
    intro stage left right extra
    change General.QuantitativeComparison
      ((schedule orders stage).comp (eliminate orders stage
        (left stage (by simp [MACNormalization.relators, Plan.needs, MACNormalization.layout]))))
      (eliminate orders (stage + 1)
        (right (stage + 1) (by simp [MACNormalization.relators, Plan.needs, MACNormalization.layout])))
    unfold schedule eliminate
    apply General.QuantitativeReduction.observe_comp
    intro n epsilon
    rfl

theorem arbitrary_comparison (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) :
    General.QuantitativeComparison
      (Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _))
      (eliminate orders stage (GameCoherence.Examples.MAC.full_security (orders stage))) := by
  exact Quantitative.evaluateCell (model orders)
    (terminalCoherence MACNormalization.strategy MACNormalization.diamonds plan (MACNormalization.direct stage))
    (MACNormalization.conditions orders _)

theorem emitted_code (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (code : Code) :
    (Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).compiler.run code = code :=
  (arbitrary_comparison orders plan).programs code

theorem resources (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F A)
    (witness : (object orders (.stage stage)).Witness F A) :
    ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).mapWitness F A witness).resources =
      witness.resources :=
  (arbitrary_comparison orders plan).resources F A witness

theorem extracted_execution (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F A)
    (witness : (object orders (.stage stage)).Witness F A) :
    ExecutionContract
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).compiler.run witness.code)
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).mapWitness F A witness).resources :=
  (Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).toTransform.compiler_executes F A witness

theorem extracted_full_observation (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F A)
    (witness : (object orders (.stage stage)).Witness F A) (order : Schedule 8) :
    (run ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).compiler.run witness.code)
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).mapWitness F A witness).resources).map
      Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observe = GameCoherence.Examples.MAC.fullLaw order :=
  (Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).toTransform.compiler_realizes F A witness order

theorem loss (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (n : Nat) (epsilon : ℝ≥0∞) :
    (Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).reduction.loss.eval n epsilon =
      epsilon + (256 : ℝ≥0∞)⁻¹ :=
  (arbitrary_comparison orders plan).loss n epsilon


theorem statisticalLoss_not_negligible : ¬ statisticalLoss.PreservesNegligible := by
  intro preserves
  have bounded := preserves (fun _ => 0) Negligible.zero 0
  obtain ⟨n, bound, large⟩ := (bounded.and (Filter.eventually_ge_atTop 256)).exists
  have upper : (256 : ℝ≥0∞)⁻¹ ≤ ((n + 1 : Nat) : ℝ≥0∞)⁻¹ := by
    simpa only [statisticalLoss, zero_add, invPoly, pow_one] using bound
  have lower : ((n + 1 : Nat) : ℝ≥0∞)⁻¹ < (256 : ℝ≥0∞)⁻¹ := by
    apply ENNReal.inv_lt_inv.mpr
    exact_mod_cast (by omega : 256 < n + 1)
  exact (not_lt_of_ge upper) lower

theorem extracted_process (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F A)
    (witness : (object orders (.stage stage)).Witness F A)
    (oracle : BitOracle State) (frame : Configuration State) (horizon : Nat) :
    TimedExecution.eval (Reification.timedStep
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).compiler.run witness.code) oracle)
      horizon frame = TimedExecution.eval (Reification.timedStep witness.code oracle) horizon frame := by
  rw [emitted_code]

theorem stage_probability_realized (orders : Nat → Schedule 8) (stage : Nat) (F A)
    (witness : (object orders (.stage stage)).Witness F A) (n : Nat) :
    advantageProfile (object orders (.stage stage)).goal F A n =
      eventProb ((run witness.code witness.resources).map Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observe)
        (fun out => out.result = true) := by
  change eventProb (GameCoherence.Examples.MAC.fullLaw (orders stage)) (fun out => out.result = true) = _
  exact congrArg (fun law : PMF FullOutcome => eventProb law (fun out => out.result = true))
    (witness.realizes (orders stage)).symm

theorem sanitized_observation (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F A)
    (witness : (object orders (.stage stage)).Witness F A) (order : Schedule 8) :
    ((run ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).compiler.run witness.code)
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).mapWitness F A witness).resources).map
      Foundation.Symmetric.RandomFunctionMACNativeCaller.Native.observe).map MACNormalization.sanitize =
      (GameCoherence.Examples.MAC.fullLaw order).map MACNormalization.sanitize :=
  congrArg (fun law => law.map MACNormalization.sanitize) (extracted_full_observation orders plan F A witness order)

theorem arbitrary_bound (orders : Nat → Schedule 8) {stage : Nat}
    (plan : Plan MACNormalization.layout (.stage stage) .finish) (F) :
    (object orders (.stage stage)).Bounded F (fun _ => (256 : ℝ≥0∞)⁻¹) := by
  have target : (object orders .finish).Bounded
      ((Quantitative.evaluate (base orders) plan (MACNormalization.conditions orders _)).reduction.mapFamily F)
      (fun _ => 0) := by
    intro A admissible n
    exact le_rfl
  have result := Quantitative.bounded (base orders) plan (MACNormalization.conditions orders _) F (fun _ => 0) target
  have same : (fun n => (Quantitative.evaluate (base orders) plan
      (MACNormalization.conditions orders _)).reduction.loss.eval n 0) = (fun _ => (256 : ℝ≥0∞)⁻¹) := by
    funext n
    rw [loss, zero_add]
  rw [same] at result
  exact result

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNativeQuantitative
