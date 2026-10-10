import Foundation.Quantum.SpectralGeneratorStages
import Foundation.Examples.QuantumContexts

/-! Two distinguishable characters of the concrete algebra ℂ×ℂ. These
examples are our own; they check that the spectral logic is not collapsed. -/
namespace Foundation.Quantum.ContextExamples
noncomputable section
open Foundation.Logic
open Bohr.GeneratorLogic
set_option backward.isDefEq.respectTransparency false

/-- The first coordinate is a nonzero multiplicative continuous functional. -/
def firstCharacter : fullContext.Spectrum :=
  ⟨{ toLinearMap := {
       toFun := fun a => a.val.1
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl }
     cont := continuous_fst.comp continuous_subtype_val },
    by
      constructor
      · intro h
        have hh := congrArg (fun f : WeakDual ℂ fullContext.algebra => f 1) h
        exact one_ne_zero hh
      · intro x y
        rfl⟩

/-- The second coordinate supplies a different physical classical alternative. -/
def secondCharacter : fullContext.Spectrum :=
  ⟨{ toLinearMap := {
       toFun := fun a => a.val.2
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl }
     cont := continuous_snd.comp continuous_subtype_val },
    by
      constructor
      · intro h
        have hh := congrArg (fun f : WeakDual ℂ fullContext.algebra => f 1) h
        exact one_ne_zero hh
      · intro x y
        rfl⟩

def spectralObservation : fullContext.algebra := ⟨observation, by trivial⟩

theorem first_not_positive : firstCharacter ∉ fullContext.positiveOpen spectralObservation := by
  change ¬ (0 : ℝ) < 0
  exact lt_irrefl _

theorem second_positive : secondCharacter ∈ fullContext.positiveOpen spectralObservation := by
  change (0 : ℝ) < 1
  norm_num

theorem spectralObservation_proper :
    fullContext.positiveOpen spectralObservation ≠ ⊥ ∧
    fullContext.positiveOpen spectralObservation ≠ ⊤ := by
  constructor
  · intro h
    have hh := second_positive
    rw [h] at hh
    exact hh
  · intro h
    apply first_not_positive
    rw [h]
    trivial

/-- The actual composite finite derivation is interpreted in a two-point spectrum. -/
theorem additionCover_interpreted :
    (model fullContext).Carrier
      (.positive (spectralObservation+spectralObservation),
       .join (.regularCover spectralObservation) (.regularCover spectralObservation)) :=
  sound fullContext (additionCoverProof fullContext spectralObservation spectralObservation)
    (fun i => Fin.elim0 i)

/-- A false entailment remains unprovable: the observation is positive at
 one character and fails at the other. No semantic-truth rule is available. -/
theorem positivity_not_derivable : IsEmpty
    (Logic.Derivation (presentation fullContext) (Logic.Context.empty (presentation fullContext))
      (.top,.positive spectralObservation)) where
  false d := first_not_positive ((sound fullContext d (fun i => Fin.elim0 i)) (by trivial))

/-- Both local truth values survive inside the external stage frame. -/
theorem stage_positive_distinguished :
    (⟨fullContext,secondCharacter⟩ : Bohr.SpectrumBundle Algebra) ∈
      (stageEval fullContext (.positive spectralObservation)).val ∧
    (⟨fullContext,firstCharacter⟩ : Bohr.SpectrumBundle Algebra) ∉
      (stageEval fullContext (.positive spectralObservation)).val := by
  constructor
  · change secondCharacter ∈ (stageEval fullContext (.positive spectralObservation)).val.fiber fullContext
    rw [stageEval_fiber]
    exact second_positive
  · change firstCharacter ∉ (stageEval fullContext (.positive spectralObservation)).val.fiber fullContext
    rw [stageEval_fiber]
    exact first_not_positive

/-- The same composite derivation now has an actual stage-frame interpretation. -/
theorem additionCover_stage_interpreted :
    (stageModel fullContext).Carrier
      (.positive (spectralObservation+spectralObservation),
       .join (.regularCover spectralObservation) (.regularCover spectralObservation)) :=
  stage_sound fullContext (additionCoverProof fullContext spectralObservation spectralObservation)
    (fun i => Fin.elim0 i)

end
end Foundation.Quantum.ContextExamples
