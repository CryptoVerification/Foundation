import Foundation.Crypto.Semantics.Probability.GeneralVariationObservers

/-! Source-dependent deterministic output maps contract conditional distance.
Retaining any correlated register preserves it exactly. No finiteness or
independence assumption on the input or register type is required. -/
namespace Foundation.Probability.GeneralKernelVariation
open scoped BigOperators ENNReal
noncomputable section
variable {A B C D E : Type}

theorem mapped (p : PMF D) (read : D → A) (emit : D → B → E) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (emit s)) (fun s => (g (read s)).map (emit s)) ≤ distance (p.map read) f g := by
  unfold distance
  rw [map_average]
  exact ENNReal.tsum_le_tsum (fun s => mul_le_mul_right (map_contraction _ _ _) _)

theorem mapped_eq (p : PMF D) (read : D → A) (emit : D → B → E) (recover : D → E → B)
    (f g : A → PMF B) (inverse : ∀ s y, recover s (emit s y) = y) :
    distance p (fun s => (f (read s)).map (emit s)) (fun s => (g (read s)).map (emit s)) = distance (p.map read) f g := by
  unfold distance
  rw [map_average]
  apply tsum_congr
  intro s
  exact congrArg (p s * ·) (map_isometry (f (read s)) (g (read s)) (emit s) (recover s) (inverse s))

theorem frame (p : PMF D) (read : D → A) (retain : D → C) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (fun y => (y,retain s)))
      (fun s => (g (read s)).map (fun y => (y,retain s))) ≤ distance (p.map read) f g :=
  mapped p read (fun s y => (y,retain s)) f g

theorem frame_eq (p : PMF D) (read : D → A) (retain : D → C) (f g : A → PMF B) :
    distance p (fun s => (f (read s)).map (fun y => (y,retain s)))
      (fun s => (g (read s)).map (fun y => (y,retain s))) = distance (p.map read) f g := by
  unfold distance
  rw [map_average]
  apply tsum_congr
  intro s
  exact congrArg (p s * ·) (map_isometry (f (read s)) (g (read s)) (fun y => (y,retain s)) Prod.fst (fun _ => rfl))

end
end Foundation.Probability.GeneralKernelVariation
