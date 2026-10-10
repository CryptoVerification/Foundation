import Foundation.Quantum.QKD.HashDistanceLogic

/-! Actual positive fourth roots and inverse-fourth-root reconstruction for a
faithful finite reference state. Singular references require support-restricted
inverses and are not silently treated as invertible. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

/-- The positive fourth root obtained by applying the functional calculus twice. -/
def quarterRoot (T : Operator e) : Operator e := CFC.sqrt (CFC.sqrt T)

theorem quarterRoot_positive (T : Operator e) : (quarterRoot T).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt T))

theorem quarterRoot_square (T : Operator e) : quarterRoot T * quarterRoot T = CFC.sqrt T :=
  CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg T)

theorem quarterRoot_fourth (T : Operator e) (hT : T.PosSemidef) :
    ((quarterRoot T)*(quarterRoot T).conjTranspose)*
      ((quarterRoot T)*(quarterRoot T).conjTranspose) = T := by
  rw [(quarterRoot_positive T).isHermitian.eq, quarterRoot_square]
  exact CFC.sqrt_mul_sqrt_self T hT.nonneg

theorem quarterRoot_isUnit (T : Operator e) (hT : T.PosSemidef) (hunit : IsUnit T) :
    IsUnit (quarterRoot T) :=
  (CFC.isUnit_sqrt_iff _ (CFC.sqrt_nonneg T)).mpr ((CFC.isUnit_sqrt_iff T hT.nonneg).mpr hunit)

/-- A faithful reference supplies actual reconstruction matrices for every
input operator; no observation-distance conclusion is a premise. -/
theorem inverse_quarter_reconstruct (T B : Operator e) (hT : T.PosSemidef) (hunit : IsUnit T) :
    B = (quarterRoot T).conjTranspose *
      ((quarterRoot T)⁻¹ * B * ((quarterRoot T)⁻¹).conjTranspose) * quarterRoot T := by
  let D := quarterRoot T
  have hd : D.IsHermitian := (quarterRoot_positive T).isHermitian
  have hu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp (quarterRoot_isUnit T hT hunit)
  change B = D.conjTranspose * (D⁻¹ * B * (D⁻¹).conjTranspose) * D
  rw [hd.eq, Matrix.conjTranspose_nonsing_inv, hd.eq]
  calc
    B = (D*D⁻¹)*B*(D⁻¹*D) := by rw [Matrix.mul_nonsing_inv D hu, Matrix.nonsing_inv_mul D hu]; simp
    _ = D*(D⁻¹*B*D⁻¹)*D := by simp only [Matrix.mul_assoc]

/-- Finite privacy-amplification observation bound for a normalized faithful
reference: the reconstruction cost is exactly one, not the side dimension.
The public seed is part of the jointly observed output. -/
theorem faithful_reference_distance {X Y S : Type} [Fintype X] [Fintype Y]
    [Nonempty Y] [DecidableEq Y] [Fintype S]
    (p : PMF S) (h : S → X → Y) (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef)
    (τ : Density e) (hτ : IsUnit τ.matrix)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox (publicMixture p (fun s => hashed B (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) B))
        ((1/2:ℝ)*Real.sqrt (Fintype.card Y * input (sandwich (quarterRoot τ.matrix)⁻¹ B))) := by
  have hb := published_two_universal p h B hB (quarterRoot τ.matrix)⁻¹ (quarterRoot τ.matrix)
    (fun x => inverse_quarter_reconstruct τ.matrix (B x) τ.positive hτ) hδ
  simpa only [quarterRoot_fourth τ.matrix τ.positive, τ.normalized, Complex.one_re, mul_one] using hb

/-- The reference roots discharge the reconstruction and cost premises of the
existing finite derivation; only a concrete input collision bound remains. -/
theorem faithful_reference_interpreted {X Y S : Type} [Fintype X] [Fintype Y]
    [Nonempty Y] [DecidableEq Y] [Fintype S]
    (p : PMF S) (h : S → X → Y) (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef)
    (τ : Density e) (hτ : IsUnit τ.matrix) (q : ℝ)
    (hq : input (sandwich (quarterRoot τ.matrix)⁻¹ B) ≤ q)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox (publicMixture p (fun s => hashed B (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) B))
        ((1/2:ℝ)*Real.sqrt (Fintype.card Y * ((1-1/Fintype.card Y)*q))) := by
  apply HashDistanceLogic.sound p h (fun _ => B) (fun _ => hB)
    (fun _ => (quarterRoot τ.matrix)⁻¹) (fun _ => quarterRoot τ.matrix) hδ
    (HashDistanceLogic.proof (Fintype.card Y) 0 0 q (Fintype.card Y))
  intro i
  change Fin 3 at i
  by_cases h0 : i = 0
  · subst i
    change ∀ x, B x = (quarterRoot τ.matrix).conjTranspose * sandwich (quarterRoot τ.matrix)⁻¹ B x * quarterRoot τ.matrix
    exact fun x => inverse_quarter_reconstruct τ.matrix (B x) τ.positive hτ
  · by_cases h1 : i = 1
    · subst i
      exact hq
    · have h2 : i = 2 := by omega
      subst i
      change HashDistanceLogic.cost (Y := Y) (quarterRoot τ.matrix) ≤ Fintype.card Y
      simp only [HashDistanceLogic.cost, quarterRoot_fourth τ.matrix τ.positive,
        τ.normalized, Complex.one_re, mul_one, le_refl]

end
end Foundation.Quantum.QKD.Collision
