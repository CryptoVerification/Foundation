import Foundation.Quantum.QKD.PairwiseRawExamples
import Foundation.Quantum.StateDistanceLogic

/-! Interpret the existing finite-mixture proof on the complete BB84 raw
sampling approximation. Every premise is discharged by the actual conditional
sampling theorem, including the insufficient-sample branches. -/
namespace Foundation.Quantum.QKD.PairwiseRandomizedSampling
noncomputable section
open BB84SiftedInput Foundation.Logic StateDistanceLogic
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

abbrev branches (n : Nat) := Fintype.card (Finset (Fin n))

def matchSet {n : Nat} (i : Fin (branches n)) := (Fintype.equivFin (Finset (Fin n))).symm i

def states {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat)
    (j : Nat) : Density (BB84MixedPreparedRaw.recordSpace n e) :=
  if h : j < branches n then
    let M := matchSet ⟨j,h⟩
    Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalReal A M η k minKey tolerance)
  else if h : j - branches n < branches n then
    let M := matchSet ⟨j-branches n,h⟩
    Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalIdeal A M η k gap minKey tolerance)
  else delayedRecord A k minKey tolerance

theorem states_real {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat)
    (i : Fin (branches n)) : states A k gap minKey tolerance i.val =
      Density.mixture (Foundation.Probability.uniform (Fin (remainderCount (matchSet i)) → BB84Basis))
        (fun η => conditionalReal A (matchSet i) η k minKey tolerance) := by
  simp only [states, dif_pos i.isLt]

theorem states_ideal {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat)
    (i : Fin (branches n)) : states A k gap minKey tolerance (i.val + branches n) =
      Density.mixture (Foundation.Probability.uniform (Fin (remainderCount (matchSet i)) → BB84Basis))
        (fun η => conditionalIdeal A (matchSet i) η k gap minKey tolerance) := by
  have hn : ¬i.val + branches n < branches n := by omega
  simp only [states, dif_neg hn, Nat.add_sub_cancel_right, dif_pos i.isLt]
  apply congrArg (fun j : Fin (branches n) =>
    Density.mixture (Foundation.Probability.uniform (Fin (remainderCount (matchSet j)) → BB84Basis))
      (fun η => conditionalIdeal A (matchSet j) η k gap minKey tolerance))
  apply Fin.ext
  change i.val + branches n - branches n = i.val
  omega

/-- The ordinary finite-mixture rule combines the proved physical branches.
No new judgment, rule, kernel extension or arbitrary truth rule is added. -/
theorem randomized_interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    (StateDistanceLogic.model (states A k gap minKey tolerance) (fun _ => Channel.identity _)).Carrier
      ⟨.mixture (branches n) (Foundation.Probability.uniform (Fin (branches n))) (fun i => .state i.val),
       .mixture (branches n) (Foundation.Probability.uniform (Fin (branches n)))
         (fun i => .state (i.val + branches n)),
       ∑ i : Fin (branches n), (Foundation.Probability.uniform (Fin (branches n)) i).toReal *
         conditionalError (matchSet i) k gap⟩ := by
  apply StateDistanceLogic.sound _ _
    (mixtureProof (branches n) (Foundation.Probability.uniform (Fin (branches n)))
      (fun i => .state i.val) (fun i => .state (i.val + branches n))
      (fun i => conditionalError (matchSet i) k gap))
  intro i
  change StateApprox (states A k gap minKey tolerance i.val)
    (states A k gap minKey tolerance (i.val + branches n)) _
  rw [states_real, states_ideal]
  exact StateApprox.mixture_uniform_bound _ _ _
    (fun η => conditional_approximation A (matchSet i) η k gap minKey tolerance)

/-- The interpreted left term is the existing full randomized raw state,
expressed by the established delayed experiment equality. -/
theorem interpreted_real_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    ((Term.mixture (branches n) (Foundation.Probability.uniform (Fin (branches n)))
      (fun i => .state i.val)).eval (states A k gap minKey tolerance)
        (fun _ => Channel.identity _)).matrix = (delayedRecord A k minKey tolerance).matrix := by
  change (Density.mixture (Foundation.Probability.uniform (Fin (branches n)))
    (fun i : Fin (branches n) => states A k gap minKey tolerance i.val)).matrix = _
  have h := Density.mixture_uniform_equiv (Fintype.equivFin (Finset (Fin n))).symm
    (fun M => Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalReal A M η k minKey tolerance))
  apply Eq.trans _ (h.trans (real_mixture A k minKey tolerance))
  apply Density.mixture_congr_matrix
  intro i
  rw [states_real]
  rfl

/-- The interpreted right term is precisely the same constructed global
approximant, not a different ideal state chosen after the proof. -/
theorem interpreted_ideal_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    ((Term.mixture (branches n) (Foundation.Probability.uniform (Fin (branches n)))
      (fun i => .state (i.val + branches n))).eval (states A k gap minKey tolerance)
        (fun _ => Channel.identity _)).matrix = (ideal A k gap minKey tolerance).matrix := by
  change (Density.mixture (Foundation.Probability.uniform (Fin (branches n)))
    (fun i : Fin (branches n) => states A k gap minKey tolerance (i.val + branches n))).matrix = _
  have h := Density.mixture_uniform_equiv (Fintype.equivFin (Finset (Fin n))).symm
    (fun M => Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis))
      (fun η => conditionalIdeal A M η k gap minKey tolerance))
  apply Eq.trans _ h
  apply Density.mixture_congr_matrix
  intro i
  rw [states_ideal]
  rfl

/-- Reindexing the finite rule's error sum gives the original match-set
probability-weighted sampling error exactly. -/
theorem interpreted_error_eq (n k gap : Nat) :
    (∑ i : Fin (branches n), (Foundation.Probability.uniform (Fin (branches n)) i).toReal *
      conditionalError (matchSet i) k gap) = error n k gap := by
  have hw (i : Fin (branches n)) :
      Foundation.Probability.uniform (Fin (branches n)) i =
        Foundation.Probability.uniform (Finset (Fin n)) (matchSet i) := by
    simp [Foundation.Probability.uniform, PMF.uniformOfFintype_apply, branches]
  calc
    _ = ∑ i : Fin (branches n),
        (Foundation.Probability.uniform (Finset (Fin n)) (matchSet i)).toReal *
          conditionalError (matchSet i) k gap := Finset.sum_congr rfl (fun i _ => by rw [hw])
    _ = _ := Equiv.sum_comp (Fintype.equivFin (Finset (Fin n))).symm
      (fun M => (Foundation.Probability.uniform (Finset (Fin n)) M).toReal * conditionalError M k gap)

end
end Foundation.Quantum.QKD.PairwiseRandomizedSampling
