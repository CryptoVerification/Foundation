import Foundation.Quantum.QKD.SubnormalizedRelabel
import Foundation.Quantum.QKD.PrivacyAmplificationLogic

/-! Operator domination survives public disclosure with a cardinality cost.
The new public register and all older quantum side information are retained.
The reference may be singular; no guessing/optimization duality is assumed. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X C L : Type} [Fintype X] [Fintype C] [Fintype L] {e : Space}

/-- Independent uniform new public register alongside the old reference. -/
def leakedReference [Nonempty C] (τ : Density e) : Density (Guessing.publicSpace C e) where
  matrix := ClassicalBlocks.of (fun _ : C => ((1/(Fintype.card C:ℝ):ℝ):ℂ) • τ.matrix)
  positive := ClassicalBlocks.positive _ (fun _ => τ.positive.smul
    (Complex.nonneg_iff.mpr ⟨by simp only [Complex.ofReal_re]; positivity,by simp⟩))
  normalized := by
    rw [ClassicalBlocks.trace]
    simp only [Matrix.trace_smul, τ.normalized, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card C:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact_mod_cast (show (Fintype.card C:ℝ)*(1/(Fintype.card C:ℝ)) = 1 by field_simp)

theorem leakedReference_scaled [Nonempty C] (τ : Density e) (q : ℝ) :
    ((Fintype.card C*q:ℝ):ℂ) • (leakedReference (C := C) τ).matrix =
      ClassicalBlocks.of (fun _ : C => (q:ℂ) • τ.matrix) := by
  have hc : (Fintype.card C:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ((Fintype.card C*q:ℝ):ℂ) * ((1/(Fintype.card C:ℝ):ℝ):ℂ) = (q:ℂ) := by
    exact_mod_cast (show (Fintype.card C:ℝ)*q*(1/(Fintype.card C:ℝ)) = q by field_simp)
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · simp only [leakedReference, ClassicalBlocks.of, Matrix.smul_apply, h, ite_true, smul_eq_mul]
    rw [← mul_assoc, hs]
  · simp [leakedReference, ClassicalBlocks.of, Matrix.smul_apply, h]

/-- Each public branch is below the hidden block, so its domination has the
same q before writing the normalized uniform public reference. -/
theorem branch_dominated (ρ : State (X × C) e) (τ : Density e) (q : ℝ)
    (hdom : Dominated (hideLeak ρ) τ q) (x : X) (c : C) :
    (((q:ℂ) • τ.matrix)-ρ.block (x,c)).PosSemidef := by
  have hp := (hdom x).add (hidden_remainder_positive ρ x c)
  simpa only [sub_add_sub_cancel] using hp

theorem withPublic_dominated [Nonempty C] (ρ : State (X × C) e) (τ : Density e) (q : ℝ)
    (hdom : Dominated (hideLeak ρ) τ q) :
    Dominated (withPublic ρ) (leakedReference (C := C) τ) (Fintype.card C*q) := by
  intro x
  rw [leakedReference_scaled]
  have hb := ClassicalBlocks.representation (fun c : C => ρ.block (x,c))
  change (ClassicalBlocks.of (fun _ : C => (q:ℂ) • τ.matrix) -
    ∑ c, Matrix.kronecker (basisDensity _ (Fintype.equivFin C c)).matrix (ρ.block (x,c))).PosSemidef
  rw [← hb, ← ClassicalBlocks.sub]
  exact ClassicalBlocks.positive _ (fun c => branch_dominated ρ τ q hdom x c)

/-- Only the newly disclosed message costs a factor; the reference already
contains the entire old public register and the adversarial auxiliary system. -/
theorem additional_dominated [Nonempty C] (ρ : State ((X × C) × L) e)
    (τ : Density (Guessing.publicSpace L e)) (q : ℝ)
    (hdom : Dominated (withPublic (forgetMessage ρ)) τ q) :
    Dominated (withPublic (withPublic ρ)) (leakedReference (C := C) τ) (Fintype.card C*q) := by
  apply withPublic_dominated
  simpa only [hide_withPublic] using hdom

theorem disclose_dominated [Nonempty C] [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C)
    (τ : Density (Guessing.publicSpace L e)) (q : ℝ)
    (hdom : Dominated (withPublic ρ) τ q) :
    Dominated (withPublic (withPublic (disclose ρ message)))
      (leakedReference (C := C) τ) (Fintype.card C*q) := by
  apply additional_dominated
  simpa only [forget_disclose] using hdom

/-- Publishing r binary symbols costs the explicit factor 2^r. -/
theorem bit_disclose_dominated [DecidableEq X] [DecidableEq L] (r : Nat)
    (ρ : State (X × L) e) (message : X → L → (Fin r → Fin 2))
    (τ : Density (Guessing.publicSpace L e)) (q : ℝ)
    (hdom : Dominated (withPublic ρ) τ q) :
    Dominated (withPublic (withPublic (disclose ρ message)))
      (leakedReference (C := Fin r → Fin 2) τ) ((2:ℝ)^r*q) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    disclose_dominated ρ message τ q hdom

theorem mass_disclosed [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C) :
    mass (withPublic (withPublic (disclose ρ message))) = mass ρ := by
  rw [mass_withPublic, mass_withPublic]
  exact mass_relabel _ _

/-- The disclosed operator bound and conserved branch weight are passed to
an actual finite privacy-amplification derivation. -/
theorem disclose_privacy {Y S : Type} [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype S]
    [Nonempty C] [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C)
    (τ : Density (Guessing.publicSpace L e)) (q : ℝ) (hq : 0 ≤ q)
    (hdom : Dominated (withPublic ρ) τ q) (p : PMF S) (h : S → X → Y)
    (hδ : ∀ x x', x ≠ x' → Collision.collision p h x x' ≤ 1 / Fintype.card Y) :
    OperatorApprox
      (publicMixture p (fun seed => Collision.hashed (withPublic (withPublic (disclose ρ message))).block (h seed)))
      (publicMixture p (fun _ => Collision.uniformComparator (Y := Y) (withPublic (withPublic (disclose ρ message))).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card Y*((1-1/Fintype.card Y)*((Fintype.card C*q)*mass ρ)))) := by
  apply PrivacyAmplificationLogic.sound p h (fun _ => withPublic (withPublic (disclose ρ message)))
    (fun _ => leakedReference (C := C) τ) hδ
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0 (Fintype.card C*q) (mass ρ) _
      (mul_nonneg (Nat.cast_nonneg _) hq) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact disclose_dominated ρ message τ q hdom
  · have hi1 : i = 1 := by omega
    subst i
    exact le_of_eq (mass_disclosed ρ message)

end
end Foundation.Quantum.QKD.Subnormalized
