import Foundation.Crypto.Logic.Polygraph.GameProofComputational
import Foundation.Crypto.Logic.Polygraph.Experiment

/-! A balanced additive charge bag is insufficient for computational loss
composition, even when both loss functions preserve negligible advantages.
The obstruction is realized by certified identity programs on a zero
observation, so neither machine code nor execution evidence is the cause. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.ComputationalLossBoundary
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def twice : AdvantageBound where
  eval _ ε := ε + ε
  monotone _ _ _ bound := add_le_add bound bound

noncomputable def prefixError : AdvantageBound where
  eval n ε := if n = 0 then ε + 1 else ε
  monotone n _ _ bound := by
    by_cases zero : n = 0
    · simpa only [if_pos zero] using add_le_add bound (le_refl (1 : ℝ≥0∞))
    · simp only [if_neg zero]; exact bound

theorem twice_negligible : twice.PreservesNegligible := fun _ negligible => negligible.add negligible

theorem prefixError_negligible : prefixError.PreservesNegligible := by
  intro ε negligible
  apply (Negligible.congr (ε := ε) (δ := fun n => prefixError.eval n (ε n)) _).mp negligible
  filter_upwards [Filter.eventually_ge_atTop 1] with n positive
  simp only [prefixError, if_neg (by omega : n ≠ 0)]

variable {K : General.CodeSystem} {machine : K.Machine}

def observedZero (object : General.SecurityObject.{0, 0} K machine) :=
  Experiment.observe object (fun _ _ _ => 0)

def identityWithLoss (object : General.SecurityObject.{0, 0} K machine) (loss : AdvantageBound)
    (negligible : loss.PreservesNegligible) : General.CertifiedReduction (observedZero object) (observedZero object) where
  reduction := {
    mapInstance := id
    reduce := fun _ observer => observer
    loss := loss
    advantage_le := by intro n input observer; exact zero_le}
  compiler := .identity machine
  mapWitness := fun _ _ witness => witness
  code_eq := by intros; rfl
  negligible := negligible

noncomputable def firstOrder (object : General.SecurityObject.{0, 0} K machine) :=
  (identityWithLoss object twice twice_negligible).comp (identityWithLoss object prefixError prefixError_negligible)

noncomputable def secondOrder (object : General.SecurityObject.{0, 0} K machine) :=
  (identityWithLoss object prefixError prefixError_negligible).comp (identityWithLoss object twice twice_negligible)

theorem same_program (object : General.SecurityObject.{0, 0} K machine) (code : K.Code machine) :
    (firstOrder object).compiler.run code = (secondOrder object).compiler.run code := rfl

theorem same_packet (object : General.SecurityObject.{0, 0} K machine) (packet : (observedZero object).Packet) :
    (firstOrder object).runPacket packet = (secondOrder object).runPacket packet := rfl

theorem different_loss (object : General.SecurityObject.{0, 0} K machine) :
    (firstOrder object).reduction.loss.eval 0 0 = 2 ∧ (secondOrder object).reduction.loss.eval 0 0 = 1 := by
  constructor <;> norm_num [firstOrder, secondOrder, identityWithLoss, General.CertifiedReduction.comp,
    Reduction.comp, AdvantageBound.comp, twice, prefixError]

theorem no_comparison (object : General.SecurityObject.{0, 0} K machine) :
    ¬General.CertifiedComparison (firstOrder object) (secondOrder object) := by
  intro comparison
  have impossible := comparison.loss 0 0
  rw [(different_loss object).1, (different_loss object).2] at impossible
  norm_num at impossible

def layout : Layout Unit Bool Unit Bool where
  source _ := ()
  target _ := ()
  needs _ := ∅
  charges label := {label}

def left : Plan layout () () := .seq (.atom false) (.atom true)
def right : Plan layout () () := .seq (.atom true) (.atom false)

theorem same_charge_bag : left.charges layout = right.charges layout := add_comm _ _

noncomputable def model (object : General.SecurityObject.{0, 0} K machine) :
    Computational.Model K layout (fun _ => True) where
  machine _ := machine
  object _ := observedZero object
  atom label _ := if label then identityWithLoss object prefixError prefixError_negligible
    else identityWithLoss object twice twice_negligible

def relators (_ : Unit) : Relator layout where
  source := ()
  target := ()
  left := left
  right := right
  needs := ∅
  balanced := same_charge_bag

/-- The syntax admits a charge-balanced root, but that root cannot be
interpreted in this checked computational model. -/
theorem no_higher_model (object : General.SecurityObject.{0, 0} K machine) :
    ¬∃ higher : Computational.HigherModel K layout relators (fun _ => True), higher.base = model object := by
  rintro ⟨higher, base⟩
  have comparison := higher.comparison () (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  rw [base] at comparison
  exact no_comparison object comparison

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.ComputationalLossBoundary
