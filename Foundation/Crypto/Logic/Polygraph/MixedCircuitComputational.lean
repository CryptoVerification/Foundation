import Foundation.Crypto.Logic.Polygraph.MixedCircuitNormalization
import Foundation.Crypto.Logic.Polygraph.ComputationalComparison
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! Computational interpretation of actual directed mixed rewrite paths.
Every contextual step requires a certified reduction, not merely equality of
stochastic kernels. Formal inverse tracks have no interpreter here. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Computational
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.General
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

structure Model (K : CodeSystem) (relators : Rule → Relator signature) (condition : Requirement → Prop) where
  machine : {n m : Port signature} → Circuit signature n m → K.Machine
  object : ∀ {n m} (circuit : Circuit signature n m), General.SecurityObject.{0, 0} K (machine circuit)
  step : ∀ {n m} {a b : Circuit signature n m} (change : Step relators a b),
    Holds condition change.support → General.CertifiedReduction (object a) (object b)

def extract {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition) :
    {n m : Port signature} → {a b : Circuit signature n m} → (path : Path (relators := relators) a b) →
    Holds condition (Path.support path) → General.CertifiedReduction (model.object a) (model.object b)
  | _, _, _, _, .refl a, _ => .id (model.object a)
  | _, _, _, _, .cons change tail, valid =>
      (model.step change (valid.restrict Finset.subset_union_left)).comp
        (extract model tail (valid.restrict Finset.subset_union_right))

theorem extract_single {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition)
    {n m} {a b : Circuit signature n m} (change : Step relators a b)
    (valid : Holds condition (Path.support (Foundation.Logic.Polygraph.RewritePath.single change))) :
    CertifiedComparison (extract model (Foundation.Logic.Polygraph.RewritePath.single change) valid)
      (model.step change (valid.restrict (by rw [Path.single_support]))) :=
  by
    simpa only [extract, Foundation.Logic.Polygraph.RewritePath.single] using
      (CertifiedComparison.rightUnit (model.step change
        (valid.restrict (by rw [Path.single_support]))))

theorem extract_comp {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition)
    {n m} {a b c : Circuit signature n m} (first : Path (relators := relators) a b)
    (second : Path (relators := relators) b c)
    (one : Holds condition (Path.support first)) (two : Holds condition (Path.support second))
    (both : Holds condition (Path.support (first.comp second))) :
    CertifiedComparison ((extract model first one).comp (extract model second two))
      (extract model (first.comp second) both) := by
  induction first with
  | refl =>
      simpa only [extract, Foundation.Logic.Polygraph.RewritePath.comp] using
        (CertifiedComparison.leftUnit (extract model second two))
  | cons change tail ih =>
      let head := model.step change (one.restrict Finset.subset_union_left)
      simpa only [extract, Foundation.Logic.Polygraph.RewritePath.comp] using
        (CertifiedComparison.assoc head (extract model tail (one.restrict Finset.subset_union_right))
          (extract model second two)).trans
          ((CertifiedComparison.refl head).comp (ih second (one.restrict Finset.subset_union_right) two
            (both.restrict Finset.subset_union_right)))

theorem executes {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition)
    {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b)
    (valid : Holds condition (Path.support path)) (F A) (witness : (model.object a).Witness F A) :
    (model.object b).execution.ExecutesWithin
      ((extract model path valid).reduction.mapFamily F)
      ((extract model path valid).compiler.run witness.code)
      ((extract model path valid).mapWitness F A witness).resources :=
  (extract model path valid).toTransform.compiler_executes F A witness

theorem realizes {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition)
    {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b)
    (valid : Holds condition (Path.support path)) (F A) (witness : (model.object a).Witness F A) :
    (model.object b).execution.Realizes
      ((extract model path valid).reduction.mapFamily F)
      ((extract model path valid).reduction.mapAdversaryFamily F A)
      ((extract model path valid).compiler.run witness.code)
      ((extract model path valid).mapWitness F A witness).resources :=
  (extract model path valid).toTransform.compiler_realizes F A witness

theorem bounded {K : CodeSystem} {condition : Requirement → Prop} (model : Model K relators condition)
    {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b)
    (valid : Holds condition (Path.support path)) (F epsilon)
    (hypothesis : (model.object b).Bounded ((extract model path valid).reduction.mapFamily F) epsilon) :
    (model.object a).Bounded F (fun n => (extract model path valid).reduction.loss.eval n (epsilon n)) :=
  (extract model path valid).bounded F epsilon hypothesis

def repaired {K : CodeSystem} {old updated : Requirement → Prop} (model : Model K relators updated)
    {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b)
    (changed : Finset Requirement) (cached : Holds old (Path.support path))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (Path.support path) changed)) :
    General.CertifiedReduction (model.object a) (model.object b) :=
  extract model path (repair cached unchanged rechecked)

end CryptoLogic.Polygraph.MixedCircuit.Computational
