import Foundation.Quantum.SpectralExtension
import Foundation.Quantum.SpectralGeneratorLogic

/-! The generating calculus has a faithful interpretation in the external
stage frame, not just isolated local character spectra. -/
namespace Foundation.Quantum.Bohr.GeneratorLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CStarAlgebra A]

def stageEval (C : Bohr.Context A) (P : Term C) : StageFrame C := liftLocal C (eval C P)

theorem stage_valid_iff (C : Bohr.Context A) (P Q : Term C) :
    stageEval C P ≤ stageEval C Q ↔ eval C P ≤ eval C Q := liftLocal_le_iff C _ _

/-- Faithful lifting supplies actual operations for every syntactic rule. -/
def stageModel (C : Bohr.Context A) : Model (presentation C) where
  Carrier j := stageEval C j.1 ≤ stageEval C j.2
  operation := fun r h => (stage_valid_iff C _ _).mpr
    ((model C).operation r (fun i => (stage_valid_iff C _ _).mp (h i)))

theorem stage_sound (C : Bohr.Context A) {Γ : Logic.Context (presentation C)} {j}
    (d : Derivation (presentation C) Γ j)
    (h : ∀ i, (stageModel C).Carrier (Γ.claim i)) : (stageModel C).Carrier j :=
  d.eval (stageModel C) h

theorem stage_interpretation_substitute (C : Bohr.Context A)
    {Γ Δ : Logic.Context (presentation C)} {j} (d : Derivation (presentation C) Γ j)
    (r : ∀ i, Derivation (presentation C) Δ (Γ.claim i))
    (h : ∀ i, (stageModel C).Carrier (Δ.claim i)) :
    (d.substitute r).eval (stageModel C) h =
      d.eval (stageModel C) (fun i => (r i).eval (stageModel C) h) :=
  Derivation.eval_substitute (stageModel C) h d r

/-- The local meaning of a lifted syntactic proposition is exactly its original meaning. -/
theorem stageEval_fiber (C : Bohr.Context A) (P : Term C) :
    (stageEval C P).val.fiber C = eval C P := extendLocal_fiber_self C _

end
end Foundation.Quantum.Bohr.GeneratorLogic
