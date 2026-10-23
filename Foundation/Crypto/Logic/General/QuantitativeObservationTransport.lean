import Foundation.Crypto.Logic.General.QuantitativeObservation

/-! A code-changing certified transform commutes with observation changes
when its two quantitative routes have the same actual loss transformer.
The square keeps the transformed resource/execution packet, not just laws. -/
namespace CryptoLogic.General.QuantitativeReduction
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m n : K.Machine}
  {X : SecurityObject.{0, 0} K m} {Y : SecurityObject.{0, 0} K n}

def transport (T : CertifiedTransform X Y)
    (first : Polygraph.Experiment.Observation X) (second : Polygraph.Experiment.Observation Y)
    (loss : AdvantageBound)
    (bound : ∀ n input observer, first n input observer ≤ loss.eval n
      (second n (T.transform.mapInstance input) (T.transform.reduce input observer))) :
    QuantitativeReduction (Polygraph.Experiment.observe X first) (Polygraph.Experiment.observe Y second) where
  reduction := {
    mapInstance := T.transform.mapInstance
    reduce := T.transform.reduce
    loss := loss
    advantage_le := fun {n} input observer => bound n input observer }
  compiler := T.compiler
  mapWitness := (Polygraph.Experiment.transform T first second).mapWitness
  code_eq := (Polygraph.Experiment.transform T first second).code_eq

theorem observation_square (T : CertifiedTransform X Y)
    (first middle : Polygraph.Experiment.Observation X) (next last : Polygraph.Experiment.Observation Y)
    (one two three four : AdvantageBound)
    (firstBound : ∀ n input observer, first n input observer ≤ one.eval n (middle n input observer))
    (secondBound : ∀ n input observer, middle n input observer ≤ two.eval n
      (last n (T.transform.mapInstance input) (T.transform.reduce input observer)))
    (thirdBound : ∀ n input observer, first n input observer ≤ three.eval n
      (next n (T.transform.mapInstance input) (T.transform.reduce input observer)))
    (fourthBound : ∀ n input observer, next n input observer ≤ four.eval n (last n input observer))
    (sameLoss : ∀ n epsilon, one.eval n (two.eval n epsilon) = three.eval n (four.eval n epsilon)) :
    QuantitativeComparison
      ((observe X first middle one firstBound).comp (transport T middle last two secondBound))
      ((transport T first next three thirdBound).comp (observe Y next last four fourthBound)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, sameLoss⟩

end CryptoLogic.General.QuantitativeReduction
