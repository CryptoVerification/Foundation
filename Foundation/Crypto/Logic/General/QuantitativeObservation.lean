import Foundation.Crypto.Logic.General.QuantitativeReduction
import Foundation.Crypto.Logic.Polygraph.Experiment

/-! Quantitative changes of observation on one unchanged machine experiment.
The advantage bound is supplied independently of the execution certificate. -/
namespace CryptoLogic.General.QuantitativeReduction
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m : K.Machine}

def observe (X : SecurityObject.{0, 0} K m)
    (first second : Polygraph.Experiment.Observation X) (loss : AdvantageBound)
    (bound : ∀ n input observer, first n input observer ≤ loss.eval n (second n input observer)) :
    QuantitativeReduction (Polygraph.Experiment.observe X first) (Polygraph.Experiment.observe X second) where
  reduction := {
    mapInstance := fun input => input
    reduce := fun _ observer => observer
    loss := loss
    advantage_le := fun {n} input observer => bound n input observer }
  compiler := .identity m
  mapWitness := fun _ _ witness =>
    ⟨witness.code, witness.resources, witness.executes, witness.realizes, witness.admissible⟩
  code_eq := by intros; rfl

theorem observe_code (X : SecurityObject.{0, 0} K m)
    (first second : Polygraph.Experiment.Observation X) (loss : AdvantageBound)
    (bound : ∀ n input observer, first n input observer ≤ loss.eval n (second n input observer))
    (code : K.Code m) : (observe X first second loss bound).compiler.run code = code := rfl

theorem observe_resources (X : SecurityObject.{0, 0} K m)
    (first second : Polygraph.Experiment.Observation X) (loss : AdvantageBound)
    (bound : ∀ n input observer, first n input observer ≤ loss.eval n (second n input observer))
    (F A) (witness : (Polygraph.Experiment.observe X first).Witness F A) :
    ((observe X first second loss bound).mapWitness F A witness).resources = witness.resources := rfl

theorem observe_comp (X : SecurityObject.{0, 0} K m)
    (first middle last : Polygraph.Experiment.Observation X)
    (one two direct : AdvantageBound)
    (firstBound : ∀ n input observer, first n input observer ≤ one.eval n (middle n input observer))
    (secondBound : ∀ n input observer, middle n input observer ≤ two.eval n (last n input observer))
    (directBound : ∀ n input observer, first n input observer ≤ direct.eval n (last n input observer))
    (sameLoss : ∀ n epsilon, one.eval n (two.eval n epsilon) = direct.eval n epsilon) :
    QuantitativeComparison ((observe X first middle one firstBound).comp (observe X middle last two secondBound))
      (observe X first last direct directBound) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, sameLoss⟩

end CryptoLogic.General.QuantitativeReduction
