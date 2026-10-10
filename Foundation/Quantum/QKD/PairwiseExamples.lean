import Foundation.Quantum.QKD.BB84PairwiseSource
import Foundation.Quantum.QKD.SiftingExamples

/-! The fixed-reference correspondence on an actual coherent finite-Kraus
attack, including interpreted mixtures and the public selector record.
These are semantic validation examples, not final-key secrecy theorems. -/
namespace Foundation.Quantum.QKD.PairwiseExamples
noncomputable section
open BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

theorem attacked_interpreted :
    ((actualFirst (fun _ : Fin (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 1))) => .X)
      (BB84SiftedInput.auxiliary Finset.univ .bit)).record.run
        (BB84SiftedInput.input SourceReplacementExamples.attack Finset.univ)).matrix =
      ((referenceFirst (fun _ => .X) (BB84SiftedInput.auxiliary Finset.univ .bit)).record.run
        (BB84SiftedInput.input SourceReplacementExamples.attack Finset.univ)).matrix :=
  BB84PairwiseSource.selected_interpreted _ _ _

/-- A closed derivation using the first-measurement, mixing and postprocessing
rules on the actual attacked source. The attack input is not a product state. -/
theorem mixed_interpreted :
    let ρ := BB84PreparedInput.input SourceReplacementExamples.attack
    let θ : Fin 2 → Fin 1 → BB84Basis := fun i _ => if i = 0 then .Z else .X
    (BB84PairwiseLogic.model ρ (fun _ => Channel.identity (BB84PairwiseLogic.recordSpace 1 .bit))).Carrier
      (.processed 2 θ (Foundation.Probability.uniform (Fin 2)) 0) := by
  exact BB84PairwiseLogic.sound _ _
    (BB84PairwiseLogic.proof 2 (fun i _ => if i = 0 then .Z else .X)
      (Foundation.Probability.uniform (Fin 2)) 0) (fun i => Fin.elim0 i)

/-- The random basis is explicitly public beside the error record and all
remaining quantum registers, so the observer can condition on its value. -/
theorem public_interpreted :
    publicMixture (Foundation.Probability.uniform (Fin 1 → BB84Basis))
      (fun θ => ((actualFirst θ .bit).record.run
        (BB84PreparedInput.input SourceReplacementExamples.attack)).matrix) =
      publicMixture (Foundation.Probability.uniform (Fin 1 → BB84Basis))
        (fun θ => ((referenceFirst θ .bit).record.run
          (BB84PreparedInput.input SourceReplacementExamples.attack)).matrix) :=
  BB84PairwiseSource.public_interpreted _ _

/-- The same real input used above has a nonzero joint off-diagonal entry. -/
theorem attacked_coherence :
    (BB84PreparedInput.input SourceReplacementExamples.attack).matrix
      (((0,()),(0,())),0) (((1,()),(1,())),1) = (1/2:ℂ) :=
  SiftingExamples.source_input_coherence

end
end Foundation.Quantum.QKD.PairwiseExamples
