import Foundation.Quantum.QKD.DominatedLeak
import Foundation.Quantum.QKD.GuessExamples
import Foundation.Quantum.QKD.CollisionExamples
import Foundation.Quantum.QKD.PrivacyAmplificationExamples

/-! A tight operator-coefficient cost for revealing a private uniform bit.
The coherent qubit remains in the side system. The pre-message coefficient
1/2 becomes exactly 1; a smaller post-message coefficient is impossible. -/
namespace Foundation.Quantum.QKD.DominatedLeakExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic
open Subnormalized
set_option backward.isDefEq.respectTransparency false

abbrev reference : Density .bit := PrivacyAmplificationExamples.reference

def revealed : State (Fin 2 × Fin 2) .bit := ofCQ (GuessExamples.revealedBit reference)
def exposed := withPublic revealed

theorem hidden_dominated : Dominated (hideLeak revealed) reference (1/2) := by
  intro x
  exact GuessExamples.prior_dominated reference x

theorem public_dominated : Dominated exposed (leakedReference (C := Fin 2) reference) 1 := by
  have h := withPublic_dominated revealed reference (1/2) hidden_dominated
  simpa only [exposed, Fintype.card_fin, Nat.cast_ofNat, show (2:ℝ)*(1/2) = 1 by norm_num] using h

theorem public_probability : probability exposed = 1 := by
  change probability (withPublic (ofCQ (GuessExamples.revealedBit reference))) = 1
  rw [withPublic_ofCQ, probability_ofCQ, Guessing.withPublic_optimal, GuessExamples.revealed_guessing]

/-- The cardinality factor is necessary in this actual coherent model. -/
theorem coefficient_lower_bound (τ : Density (Guessing.publicSpace (Fin 2) .bit)) (q : ℝ)
    (h : Dominated exposed τ q) : 1 ≤ q := by
  have hp := probability_le_dominated exposed τ q h
  rwa [public_probability] at hp

theorem exposed_coherence (x : Fin 2) :
    exposed.block x (Fintype.equivFin (Fin 2) x,0) (Fintype.equivFin (Fin 2) x,1) = 1/4 := by
  unfold exposed withPublic revealed ofCQ GuessExamples.revealedBit
  norm_num [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap, basisDensity,
    Matrix.diagonal_apply, reference, PrivacyAmplificationExamples.reference, prepare_plus_matrix]

def proof : Derivation (PrivacyAmplificationLogic.presentation 2)
    (PrivacyAmplificationLogic.assumptions 2 0 0 1 1) (.distance 0 (1/2)) :=
  PrivacyAmplificationLogic.proof 2 0 0 1 1 (1/2) (by norm_num) (by norm_num)

/-- The post-message domination and conserved mass discharge both premises
of the finite hash-distance derivation. The new public hash seed is retained. -/
theorem interpreted : OperatorApprox
    (publicMixture CollisionExamples.seeds (fun s => Collision.hashed exposed.block (CollisionExamples.hash s)))
    (publicMixture CollisionExamples.seeds (fun _ => Collision.uniformComparator (Y := Fin 2) exposed.block)) (1/2) := by
  apply PrivacyAmplificationLogic.sound CollisionExamples.seeds CollisionExamples.hash
    (fun _ => exposed) (fun _ => leakedReference (C := Fin 2) reference)
    (fun x x' hx => by simpa only [Fintype.card_fin, Nat.cast_ofNat] using le_of_eq (CollisionExamples.hash_collision x x' hx)) proof
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact public_dominated
  · have hi1 : i = 1 := by omega
    subst i
    change mass (withPublic (ofCQ (GuessExamples.revealedBit reference))) ≤ 1
    rw [mass_withPublic, mass_ofCQ]

end
end Foundation.Quantum.QKD.DominatedLeakExamples
