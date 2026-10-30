import Foundation.Crypto.Semantics.Probability.FiniteKernelVariation

/-! Retaining a finite register does not amplify conditional variation.
The input law may correlate the active input and the retained register.
The compared kernels depend only on the active input. -/
namespace Foundation.Probability.FiniteKernelVariation
open scoped BigOperators
noncomputable section

theorem map_contraction {A B : Type} [Fintype A] [Fintype B]
    (p q : PMF A) (f : A → B) : finiteVariation (p.map f) (q.map f) ≤ finiteVariation p q := by
  change finiteVariation (p.bind (fun a => PMF.pure (f a)))
    (q.bind (fun a => PMF.pure (f a))) ≤ _
  exact postprocess p q (fun a => PMF.pure (f a))

theorem map_isometry {A B : Type} [Fintype A] [Fintype B]
    (p q : PMF A) (f : A → B) (read : B → A) (inverse : Function.LeftInverse read f) :
    finiteVariation (p.map f) (q.map f) = finiteVariation p q := by
  have recover (law : PMF A) : (law.map f).map read = law := by
    rw [PMF.map_comp, show read ∘ f = id from funext inverse, PMF.map_id]
  exact le_antisymm (map_contraction p q f)
    (by simpa only [recover] using map_contraction (p.map f) (q.map f) read)

theorem map_average {A D : Type} [Fintype A] [Fintype D]
    (p : PMF D) (read : D → A) (weight : A → ℝ) :
    (∑ x, ((p.map read) x).toReal * weight x) = ∑ s, (p s).toReal * weight (read s) := by
  classical
  change (∑ x, ((p.bind (fun s => PMF.pure (read s))) x).toReal * weight x) = _
  simp_rw [bind_real, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [PMF.pure_apply, apply_ite, ite_mul]

theorem mapped {A B D E : Type} [Fintype A] [Fintype B] [Fintype D] [Fintype E]
    (p : PMF D) (read : D → A) (emit : D → B → E) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (emit s))
      (fun s => (g (read s)).map (emit s)) ≤ distance (p.map read) f g := by
  unfold distance
  rw [map_average]
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (map_contraction _ _ _) ENNReal.toReal_nonneg)

theorem frame {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : PMF D) (read : D → A) (retain : D → C) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (fun y => (y, retain s)))
      (fun s => (g (read s)).map (fun y => (y, retain s))) ≤ distance (p.map read) f g :=
  mapped p read (fun s y => (y, retain s)) f g

theorem frame_eq {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : PMF D) (read : D → A) (retain : D → C) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (fun y => (y, retain s)))
      (fun s => (g (read s)).map (fun y => (y, retain s))) = distance (p.map read) f g := by
  unfold distance
  rw [map_average]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg ((p s).toReal * ·)
    (map_isometry (f (read s)) (g (read s)) (fun y => (y, retain s)) Prod.fst (fun _ => rfl))

end
end Foundation.Probability.FiniteKernelVariation
