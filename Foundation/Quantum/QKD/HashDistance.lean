import Foundation.Quantum.PublicMixtureObservation
import Foundation.Quantum.ClassicalBlocks
import Foundation.Quantum.QKD.CollisionVariance

/-! The collision-to-observation step with the hash seed explicitly published.
The reference reconstruction is an algebraic obligation on input blocks; its
construction from support/inverse roots remains separate from this theorem.
No distance or secrecy conclusion is assumed. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {e : Space}

/-- The actual hashed classical register and its quantum side information. -/
def hashed [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    Operator (Guessing.publicSpace Y e) := ClassicalBlocks.of (grouped B h)

/-- The uniform classical comparator has exactly the original quantum marginal. -/
def uniformComparator (B : X → Operator e) : Operator (Guessing.publicSpace Y e) :=
  ClassicalBlocks.of (fun _ : Y => ((1 / (Fintype.card Y : ℝ) : ℝ):ℂ) • ∑ x, B x)

theorem hashed_positive [DecidableEq Y] (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) (h : X → Y) : (hashed B h).PosSemidef := by
  apply ClassicalBlocks.positive
  intro y
  apply Matrix.posSemidef_sum
  intro x _
  by_cases hx : h x = y
  · simpa only [hx, ite_true] using hB x
  · simp only [hx, ite_false]; exact Matrix.PosSemidef.zero

theorem uniformComparator_positive (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) : (uniformComparator (Y := Y) B).PosSemidef := by
  apply ClassicalBlocks.positive
  intro _
  apply (Matrix.posSemidef_sum Finset.univ (fun x _ => hB x)).smul
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Complex.ofReal_re]; positivity
  · simp

theorem hashed_trace_input [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    (hashed B h).trace = (∑ x, B x).trace := by
  unfold hashed
  rw [ClassicalBlocks.trace (grouped B h), ← Matrix.trace_sum, grouped_marginal]

theorem hashed_difference [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    hashed B h - uniformComparator (Y := Y) B = ClassicalBlocks.of (deviation B h) :=
  (ClassicalBlocks.sub (grouped B h) (fun _ : Y => ((1 / (Fintype.card Y : ℝ) : ℝ):ℂ) • ∑ x, B x)).symm

theorem hashed_trace [Nonempty Y] [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    (hashed B h).trace = (uniformComparator (Y := Y) B).trace := by
  have hcc : (Fintype.card Y : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold hashed uniformComparator
  rw [ClassicalBlocks.trace (grouped B h), ClassicalBlocks.trace (fun _ : Y => ((1 / (Fintype.card Y : ℝ) : ℝ):ℂ) • ∑ x, B x)]
  simp only [Matrix.trace_smul,
    smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Matrix.trace_sum, grouped_marginal]
  push_cast
  field_simp

omit [Fintype S] in
theorem deviation_hermitian [DecidableEq Y] (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) (h : X → Y) (y : Y) : (deviation B h y).IsHermitian := by
  have hg : (grouped B h y).PosSemidef := Matrix.posSemidef_sum _ (fun x _ => by
    by_cases hx : h x = y
    · simpa only [hx, ite_true] using hB x
    · simp only [hx, ite_false]; exact Matrix.PosSemidef.zero)
  have hm := Matrix.posSemidef_sum Finset.univ (fun x _ => hB x)
  have hq : (0:ℂ) ≤ ((1 / (Fintype.card Y : ℝ) : ℝ):ℂ) := by
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [Complex.ofReal_re]; positivity
    · simp
  exact hg.isHermitian.sub (hm.smul hq).isHermitian

omit [Fintype S] in
theorem deviation_reconstruct [DecidableEq Y] (B : X → Operator e) (W D : Operator e)
    (hrec : ∀ x, B x = D.conjTranspose*sandwich W B x*D) (h : X → Y) (y : Y) :
    deviation B h y = D.conjTranspose * deviation (sandwich W B) h y * D := by
  have hg : grouped B h y = D.conjTranspose * grouped (sandwich W B) h y * D := by
    simp only [grouped, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : h x = y
    · simpa only [hx, ite_true] using hrec x
    · simp [hx]
  have hm : (∑ x, B x) = D.conjTranspose * (∑ x, sandwich W B x) * D := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl (fun x _ => hrec x)
  simp only [deviation, hg, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- A full joint observation bound, keeping the freshly sampled public seed.
Its square is controlled by the average centered weighted collision. -/
theorem published_distance [Nonempty Y] [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef) (W D : Operator e)
    (hrec : ∀ x, B x = D.conjTranspose*sandwich W B x*D) :
    OperatorApprox (publicMixture p (fun s => hashed B (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) B))
        ((1/2:ℝ) * Real.sqrt ((Fintype.card Y *
          ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re) * variance p h (sandwich W B))) := by
  have hb := publicMixture_of_factors p (fun s => hashed B (h s))
    (fun _ => uniformComparator (Y := Y) B)
    (fun s => ClassicalBlocks.of (deviation (sandwich W B) (h s)))
    (ClassicalBlocks.of (fun _ : Y => D))
    (fun s => ClassicalBlocks.hermitian _ (deviation_hermitian _ (sandwich_positive W B hB) (h s)))
    (fun s => by rw [hashed_difference]; exact ClassicalBlocks.reconstruct _ _ D (deviation_reconstruct B W D hrec (h s)))
    (fun s => hashed_trace B (h s))
  rw [ClassicalBlocks.constant_cost (X := Y) D] at hb
  have hs (s : S) := ClassicalBlocks.trace_square (deviation (sandwich W B) (h s))
  simp_rw [hs] at hb
  exact hb

/-- Two-universal hashing converts the weighted input collision into a bound
against the uniform comparator, with all published seeds and quantum side
information observed jointly. The same input is fixed before seed sampling. -/
theorem published_two_universal [Nonempty Y] [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef) (W D : Operator e)
    (hrec : ∀ x, B x = D.conjTranspose*sandwich W B x*D)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox (publicMixture p (fun s => hashed B (h s)))
      (publicMixture p (fun _ => uniformComparator (Y := Y) B))
        ((1/2:ℝ) * Real.sqrt ((Fintype.card Y *
          ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re) * input (sandwich W B))) := by
  apply (published_distance p h B hB W D hrec).weaken
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left (variance_le_input p h _ (sandwich_positive W B hB) hδ)
  exact mul_nonneg (Nat.cast_nonneg _) (trace_square_nonneg _ (Matrix.posSemidef_self_mul_conjTranspose D).isHermitian)

end
end Foundation.Quantum.QKD.Collision
