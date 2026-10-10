import Foundation.Quantum.QKD.HashCollision

/-! Collision bounds after an actual conjugation of all quantum blocks.
The conjugating operator is arbitrary and is not assumed to commute with the
states. Instantiating it with a suitable inverse fourth root is a separate
spectral/support construction, not a premise hidden in the collision proof. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {e : Space}

def sandwich (K : Operator e) (B : X → Operator e) (x : X) : Operator e :=
  K * B x * K.conjTranspose

omit [Fintype X] in
theorem sandwich_positive (K : Operator e) (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) (x : X) : (sandwich K B x).PosSemidef :=
  (hB x).mul_mul_conjTranspose_same K

theorem sandwich_trace (K A B : Operator e) :
    ((K * A * K.conjTranspose) * (K * B * K.conjTranspose)).trace.re =
      (A * (K.conjTranspose * K) * B * (K.conjTranspose * K)).trace.re := by
  congr 1
  calc
    _ = (K * (A * K.conjTranspose * K * B * K.conjTranspose)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((A * K.conjTranspose * K * B * K.conjTranspose) * K).trace :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

omit [Fintype X] in
theorem sandwich_pair (K : Operator e) (B : X → Operator e) (x x' : X) :
    pair (sandwich K B) x x' =
      (B x * (K.conjTranspose * K) * B x' * (K.conjTranspose * K)).trace.re :=
  sandwich_trace K _ _

omit [Fintype Y] in
theorem sandwich_grouped [DecidableEq Y] (K : Operator e) (B : X → Operator e) (h : X → Y) (y : Y) :
    grouped (sandwich K B) h y = K * grouped B h y * K.conjTranspose := by
  unfold grouped sandwich
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : h x = y <;> simp [hx]

/-- The averaged weighted quantum collision bound requires positivity,
not normalization, and hence applies to accepted subnormalized inputs. -/
theorem weighted_output_le [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef) (K : Operator e) (δ : ℝ)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ δ) :
    output p h (sandwich K B) ≤ (1-δ) * input (sandwich K B) + δ * total (sandwich K B) :=
  output_le p h _ (sandwich_positive K B hB) δ hδ

def weightedInput (R : Operator e) (B : X → Operator e) : ℝ :=
  ∑ x, (B x * R * B x * R).trace.re

def weightedTotal (R : Operator e) (B : X → Operator e) : ℝ :=
  ((∑ x, B x) * R * (∑ x, B x) * R).trace.re

def weightedOutput [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (R : Operator e) (B : X → Operator e) : ℝ :=
  ∑ s, (p s).toReal * ∑ y, (grouped B (h s) y * R * grouped B (h s) y * R).trace.re

theorem input_sandwich (K : Operator e) (B : X → Operator e) :
    input (sandwich K B) = weightedInput (K.conjTranspose * K) B := by
  unfold input weightedInput
  simp_rw [sandwich_pair]

theorem total_sandwich (K : Operator e) (B : X → Operator e) :
    total (sandwich K B) = weightedTotal (K.conjTranspose * K) B := by
  have hs : (∑ x, sandwich K B x) = K * (∑ x, B x) * K.conjTranspose := by
    simp only [sandwich, Matrix.mul_sum, Matrix.sum_mul]
  unfold total weightedTotal
  rw [hs, sandwich_trace]

theorem output_sandwich [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (K : Operator e) (B : X → Operator e) :
    output p h (sandwich K B) = weightedOutput p h (K.conjTranspose * K) B := by
  unfold output weightedOutput
  simp_rw [sandwich_grouped, sandwich_trace]

open scoped MatrixOrder in
/-- Finite weighted operator collision inequality in the form used by
Lemma 5 of Tomamichel--Schaffner--Smith--Renner. R may be any positive matrix;
its specialization to an inverse square root is not silently assumed. -/
theorem weighted_positive_le [DecidableEq Y] (p : PMF S) (h : S → X → Y)
    (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef)
    (R : Operator e) (hR : R.PosSemidef) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ δ) :
    weightedOutput p h R B ≤ weightedInput R B + δ * weightedTotal R B := by
  obtain ⟨K,hK⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  rw [Matrix.star_eq_conjTranspose] at hK
  subst R
  have hb := weighted_output_le p h B hB K δ hδ
  have hi : 0 ≤ input (sandwich K B) :=
    Finset.sum_nonneg (fun x _ => pair_nonneg _ (sandwich_positive K B hB) x x)
  rw [output_sandwich, input_sandwich, total_sandwich] at hb
  rw [input_sandwich] at hi
  nlinarith

end
end Foundation.Quantum.QKD.Collision
