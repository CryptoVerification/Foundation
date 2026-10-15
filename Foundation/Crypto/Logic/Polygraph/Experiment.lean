import Foundation.Crypto.Logic.General.Execution

/-! Changing the advantage observed by a security object leaves its actual
machine, admissibility, and execution interface in place. This construction
asserts no security: each reduction must separately prove its advantage bound. -/
namespace CryptoLogic.Polygraph

open General
open scoped ENNReal
universe u v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace Experiment

variable {K : CodeSystem} {m n : K.Machine}

abbrev Observation (X : General.SecurityObject.{u, v} K m) :=
  ∀ n (I : X.goal.Instance n), X.goal.Adversary n I → ℝ≥0∞

/-- Only the advantage changes. No state, randomness, or runtime evidence is
copied by this operation; witnesses still certify the same finite code. -/
def observe (X : General.SecurityObject.{u, v} K m) (advantage : Observation X) :
    General.SecurityObject.{u, v} K m where
  goal := { X.goal with advantage := advantage }
  execution := {
    Resources := X.execution.Resources
    ExecutesWithin := X.execution.ExecutesWithin
    Realizes := X.execution.Realizes }
  adversaries := ⟨X.adversaries.admissible⟩
  represented := X.represented

/-- A certified machine transform can be reused for new observations. Its
operational guarantee does not imply an advantage inequality. -/
def transform {X : General.SecurityObject.{u, v} K m}
    {Y : General.SecurityObject.{u, v} K n} (t : General.CertifiedTransform X Y)
    (a : Observation X) (b : Observation Y) :
    General.CertifiedTransform (observe X a) (observe Y b) where
  transform := ⟨t.transform.mapInstance, t.transform.reduce⟩
  compiler := t.compiler
  mapWitness := fun F A W =>
    let old : X.Witness F A := ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
    let new := t.mapWitness F A old
    ⟨new.code, new.resources, new.executes, new.realizes, new.admissible⟩
  code_eq := fun F A W => t.code_eq F A
    ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩

end Experiment
end CryptoLogic.Polygraph
