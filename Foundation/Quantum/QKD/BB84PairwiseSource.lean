import Foundation.Quantum.QKD.BB84PairwiseLogic
import Foundation.Quantum.QKD.BB84SiftedFullRecord

/-! Interpret the fixed-reference measurement calculus on the actual attacked,
selected BB84 source, and identify its random basis with binary pair selectors. -/
namespace Foundation.Quantum.QKD.BB84PairwiseSource
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

theorem selected_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin (BB84SiftedInput.selectedCount M) → BB84Basis) :
    ((actualFirst θ (BB84SiftedInput.auxiliary M e)).record.run (BB84SiftedInput.input A M)).matrix =
      ((referenceFirst θ (BB84SiftedInput.auxiliary M e)).record.run (BB84SiftedInput.input A M)).matrix := by
  exact BB84PairwiseLogic.sound (BB84SiftedInput.input A M)
    (fun _ => Channel.identity (BB84PairwiseLogic.recordSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M e)))
    (BB84PairwiseLogic.firstProof θ) (fun i => Fin.elim0 i)

/-- Uniform actual common BB84 bases are exactly uniform pair selectors in
the fixed-reference experiment; equality includes the full remaining quantum state. -/
theorem uniform_reference {n : Nat} {e : Space} (ρ : Density (jointSpace n e)) :
    (Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis))
      (fun θ => (actualFirst θ e).record.run ρ)).matrix =
      (Density.mixture (Foundation.Probability.uniform (Fin n → Fin 2))
        (fun s => (referenceFirst ((selectorEquiv n).symm s) e).record.run ρ)).matrix := by
  let F := fun s => (referenceFirst ((selectorEquiv n).symm s) e).record.run ρ
  calc
    _ = (Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis))
        (fun θ => (referenceFirst θ e).record.run ρ)).matrix := by
      apply Density.mixture_congr_matrix
      intro θ
      exact BB84PairwiseLogic.sound ρ (fun _ => Channel.identity (BB84PairwiseLogic.recordSpace n e))
        (BB84PairwiseLogic.firstProof θ) (fun i => Fin.elim0 i)
    _ = (Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis))
        (fun θ => F (selection θ))).matrix := by
      apply Density.mixture_congr_matrix
      intro θ
      dsimp only [F]
      rw [show selection θ = selectorEquiv n θ from rfl, Equiv.symm_apply_apply]
    _ = _ := uniform_selector F

/-- The selector is publicly retained, not averaged away. Observers can
condition any later joint measurement on its actual value. -/
theorem public_interpreted {n : Nat} {e : Space} (ρ : Density (jointSpace n e))
    (p : PMF (Fin n → BB84Basis)) :
    publicMixture p (fun θ => ((actualFirst θ e).record.run ρ).matrix) =
      publicMixture p (fun θ => ((referenceFirst θ e).record.run ρ).matrix) := by
  apply congrArg (publicMixture p)
  funext θ
  exact BB84PairwiseLogic.sound ρ (fun _ => Channel.identity (BB84PairwiseLogic.recordSpace n e))
    (BB84PairwiseLogic.firstProof θ) (fun i => Fin.elim0 i)

end
end Foundation.Quantum.QKD.BB84PairwiseSource
