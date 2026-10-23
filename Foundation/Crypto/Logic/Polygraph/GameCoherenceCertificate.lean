import Foundation.Crypto.Logic.Polygraph.GameCoherenceProduct

/-! Probabilistic game edits commute with an existing certified machine
reduction on a separate retained witness register. The register contains the
full witness, including resources and actual realization evidence. An optional
representation equality connects the source game probability to the reduction's
security goal; it is required before deriving a cryptographic advantage bound. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence
open Foundation.Probability General
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

def constantGame {A : Type u} (value : A) : Observed.{u} := ⟨A, .pure value, fun _ => True⟩

def constantMap {A B : Type u} (f : A → B) (value : A) :
    Step (constantGame value) (constantGame (f value)) :=
  Step.ofMap _ _ f (PMF.pure_map _ _) (fun _ _ => Iff.rfl)

namespace Certified
variable {K : CodeSystem} {m n : K.Machine}
  {X : General.SecurityObject.{0, 0} K m} {Y : General.SecurityObject.{0, 0} K n}
  (reduction : General.CertifiedReduction X Y) (F A) (W : X.Witness F A)
  {first last : Observed.{0}}

def certificatePath : Path (constantGame W) (constantGame (reduction.mapWitness F A W)) :=
  .step (constantMap (reduction.mapWitness F A) W)

def gameFirst (gamePath : Path first last) :
    Path (product first (constantGame W))
      (product last (constantGame (reduction.mapWitness F A W))) :=
  gamePath.parallel (certificatePath reduction F A W)

def reductionFirst (gamePath : Path first last) :
    Path (product first (constantGame W))
      (product last (constantGame (reduction.mapWitness F A W))) :=
  .seq ((certificatePath reduction F A W).right first)
    (gamePath.left (constantGame (reduction.mapWitness F A W)))

/-- Includes nonzero statistical errors, not just exact rewrites. The four-cell
preserves the complete conditional state/witness law and the exact loss. -/
def interchange (gamePath : Path first last) :
    Cell4 (gameFirst reduction F A W gamePath) (reductionFirst reduction F A W gamePath) :=
  Cell4.exchange gamePath (certificatePath reduction F A W)

theorem witness_law (gamePath : Path first last) (state : first.Outcome) :
    ((gameFirst reduction F A W gamePath).kernel (state, W)).map Prod.snd =
      PMF.pure (reduction.mapWitness F A W) := by
  simp only [gameFirst, Path.parallel_kernel, certificatePath, Path.kernel,
    constantMap, Step.ofMap, PMF.pure_map, PMF.map_bind]
  change (gamePath.kernel state).map (Function.const last.Outcome
    (reduction.mapWitness F A W)) = _
  exact PMF.map_const _ _

theorem alternate_witness_law (gamePath : Path first last) (state : first.Outcome) :
    ((reductionFirst reduction F A W gamePath).kernel (state, W)).map Prod.snd =
      PMF.pure (reduction.mapWitness F A W) := by
  rw [← (interchange reduction F A W gamePath).retained_law Prod.snd (state, W)]
  exact witness_law reduction F A W gamePath state

/-- Any further certified diagram of game edits preserves the actual full
witness value, not only the distinguished interchange above. -/
theorem edited_witness_law (gamePath : Path first last)
    (alternative : Path (product first (constantGame W))
      (product last (constantGame (reduction.mapWitness F A W))))
    (cell : Cell4 (gameFirst reduction F A W gamePath) alternative) (state : first.Outcome) :
    (alternative.kernel (state, W)).map Prod.snd = PMF.pure (reduction.mapWitness F A W) := by
  rw [← cell.retained_law Prod.snd (state, W)]
  exact witness_law reduction F A W gamePath state

theorem loss_preserved (gamePath : Path first last) :
    (gameFirst reduction F A W gamePath).loss = gamePath.loss ∧
      (reductionFirst reduction F A W gamePath).loss = gamePath.loss := by
  have original : (gameFirst reduction F A W gamePath).loss = gamePath.loss := by
    simp only [gameFirst, Path.parallel_loss, certificatePath, Path.loss, constantMap,
      Step.ofMap, add_zero]
  exact ⟨original, (interchange reduction F A W gamePath).sound.loss_eq.symm.trans original⟩

/-- The witness law refers to this exact emitted finite code and its original
backend-specific resource value. No new runtime bound is invented by a game edit. -/
theorem execution_preserved :
    (reduction.mapWitness F A W).code = reduction.compiler.run W.code ∧
    Y.execution.ExecutesWithin (reduction.reduction.mapFamily F)
      (reduction.compiler.run W.code) (reduction.mapWitness F A W).resources ∧
    Y.execution.Realizes (reduction.reduction.mapFamily F)
      (reduction.reduction.mapAdversaryFamily F A) (reduction.compiler.run W.code)
      (reduction.mapWitness F A W).resources :=
  ⟨reduction.code_eq F A W, reduction.toTransform.compiler_executes F A W,
    reduction.toTransform.compiler_realizes F A W⟩

/-- A game-to-goal representation certificate is necessary: attaching an
unrelated machine witness is not enough to obtain a security reduction. -/
theorem transformed_advantage_bound (gamePath : Path first last) (securityParameter : Nat)
    (represents : first.probability = X.goal.advantage securityParameter
      (F securityParameter) (A securityParameter)) :
    last.probability ≤ gamePath.loss + reduction.reduction.loss.eval securityParameter
      (Y.goal.advantage securityParameter
        (reduction.reduction.mapInstance (F securityParameter))
        (reduction.reduction.reduce (F securityParameter) (A securityParameter))) := by
  have difference : last.probability - first.probability ≤ gamePath.loss :=
    (le_max_right _ _).trans gamePath.sound
  have bound := tsub_le_iff_right.mp difference
  rw [represents] at bound
  exact bound.trans (add_le_add le_rfl
    (reduction.reduction.advantage_le (F securityParameter) (A securityParameter)))

end Certified
end
end CryptoLogic.Polygraph.Experiment.GameCoherence
