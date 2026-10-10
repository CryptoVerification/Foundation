import Foundation.Quantum.QKD.ClassicalCoupling

/-! Compose accepted-branch correctness and Alice-key secrecy into a common
uniform-key ideal with both private keys and all public/quantum side data.
Repair is a comparison state, not a communication step in the real protocol.
There is no division by the acceptance mass. -/
namespace Foundation.Quantum.QKD.CommonKey
noncomputable section
open scoped ComplexOrder
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {K T : Type} [Fintype K] [Nonempty K] [Fintype T] [DecidableEq K] [DecidableEq T] {e : Space}

omit [DecidableEq K] [DecidableEq T] in
theorem uniform_blocks_mass (B : (K × T) → Operator e) :
    (∑ p : K × T, ((((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, B (k,p.2)).trace.re)) =
      ∑ p, (B p).trace.re := by
  simp only [Fintype.sum_prod_type, Matrix.trace_smul, Matrix.trace_sum, Complex.re_sum,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card K:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : (Fintype.card K:ℝ)*(1/Fintype.card K) = 1 := by field_simp
  simp only [← mul_assoc, hw, one_mul]
  rw [Finset.sum_comm]

/-- Uniform Alice key with exactly the same public/quantum marginal. -/
def uniformize (ρ : State (K × T) e) : State (K × T) e where
  block p := ((1/(Fintype.card K:ℝ):ℝ):ℂ) • ∑ k, ρ.block (k,p.2)
  positive p := (Matrix.posSemidef_sum _ (fun k _ => ρ.positive (k,p.2))).smul
    (Complex.nonneg_iff.mpr ⟨by simp only [Complex.ofReal_re]; positivity,by simp⟩)
  bounded := by rw [uniform_blocks_mass]; exact ρ.bounded

omit [DecidableEq K] [DecidableEq T] in
theorem mass_uniformize (ρ : State (K × T) e) : mass (uniformize ρ) = mass ρ := uniform_blocks_mass ρ.block

def aliceView (ρ : State ((K × K) × T) e) : State (K × T) e := relabel ρ (fun p => (p.1.1,p.2))
def copyLabel (p : K × T) : (K × K) × T := ((p.1,p.1),p.2)
def repairLabel (p : (K × K) × T) : (K × K) × T := ((p.1.1,p.1.1),p.2)
def repaired (ρ : State ((K × K) × T) e) := relabel ρ repairLabel

def ideal (ρ : State ((K × K) × T) e) := relabel (uniformize (aliceView ρ)) copyLabel

omit [Nonempty K] in
theorem aliceView_block (ρ : State ((K × K) × T) e) (a : K) (t : T) :
    (aliceView ρ).block (a,t) = ∑ b, ρ.block ((a,b),t) := by
  simp [aliceView, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

omit [DecidableEq K] [DecidableEq T] in
theorem uniformize_public (ρ : State (K × T) e) (t : T) :
    (∑ a, (uniformize ρ).block (a,t)) = ∑ a, ρ.block (a,t) := by
  have hc : (Fintype.card K:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : (Fintype.card K:ℂ)*((1/(Fintype.card K:ℝ):ℝ):ℂ) = 1 := by
    exact_mod_cast (show (Fintype.card K:ℝ)*(1/Fintype.card K) = 1 by field_simp)
  ext i j
  simp only [uniformize, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hw, one_mul]

theorem ideal_block (ρ : State ((K × K) × T) e) (a b : K) (t : T) :
    (ideal ρ).block ((a,b),t) = if a = b then (uniformize (aliceView ρ)).block (a,t) else 0 := by
  simp [ideal, relabel, copyLabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem ideal_public (ρ : State ((K × K) × T) e) (t : T) :
    (∑ a, ∑ b, (ideal ρ).block ((a,b),t)) = ∑ a, ∑ b, ρ.block ((a,b),t) := by
  have hb (a b : K) := ideal_block ρ a b t
  simp_rw [hb]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [uniformize_public]
  simp_rw [aliceView_block]

def correctnessError (ρ : State ((K × K) × T) e) : ℝ :=
  ∑ p, if p.1.1 = p.1.2 then 0 else (ρ.block p).trace.re

theorem ideal_correctness (ρ : State ((K × K) × T) e) : correctnessError (ideal ρ) = 0 := by
  unfold correctnessError
  apply Finset.sum_eq_zero
  intro ⟨⟨a,b⟩,t⟩ _
  rw [ideal_block]
  by_cases h : a = b <;> simp [h]

omit [Nonempty K] in
theorem correctness_observation (ρ : State ((K × K) × T) e) :
    ((recordEvent e (fun r => let p := (Fintype.equivFin ((K × K) × T)).symm r
      p.1.1 ≠ p.1.2)).matrix * joint ρ).trace.re = correctnessError ρ := by
  rw [joint_event_observation ρ (fun p => p.1.1 ≠ p.1.2)]
  unfold correctnessError
  simp only [ite_not]

theorem correctness_le_error (ρ : State ((K × K) × T) e) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint (ideal ρ)) ε) : correctnessError ρ ≤ ε := by
  have hh := h (recordEvent e (fun r => let p := (Fintype.equivFin ((K × K) × T)).symm r
    p.1.1 ≠ p.1.2))
  rw [correctness_observation, correctness_observation, ideal_correctness, sub_zero] at hh
  exact (le_abs_self _).trans hh

omit [Nonempty K] in
theorem repaired_factor (ρ : State ((K × K) × T) e) : relabel (aliceView ρ) copyLabel = repaired ρ := by
  unfold aliceView repaired
  rw [relabel_comp]
  rfl

omit [Nonempty K] in
theorem repair_close (ρ : State ((K × K) × T) e) :
    OperatorApprox (joint ρ) (joint (repaired ρ)) (correctnessError ρ) := by
  have h := (relabel_coupling ρ repairLabel id).symm
  rw [relabel_id] at h
  have he : disagreement ρ repairLabel id = correctnessError ρ := by
    unfold disagreement correctnessError
    apply Finset.sum_congr rfl
    intro ⟨⟨a,b⟩,t⟩ _
    simp [repairLabel]
  rw [he] at h
  exact h

/-- A positive-mass or zero-mass accepted branch: correctness and Alice's
secrecy imply the full two-key observation bound by addition of errors. -/
theorem compose (ρ : State ((K × K) × T) e) (δ ε : ℝ)
    (hc : correctnessError ρ ≤ δ)
    (hs : OperatorApprox (joint (aliceView ρ)) (joint (uniformize (aliceView ρ))) ε) :
    OperatorApprox (joint ρ) (joint (ideal ρ)) (δ+ε) := by
  let C := classicalMap e (fun r => Fintype.equivFin ((K × K) × T)
    (copyLabel ((Fintype.equivFin (K × T)).symm r)))
  have hp := OperatorApprox.postprocess C hs
  change OperatorApprox (C.toKraus.apply (joint (aliceView ρ)))
    (C.toKraus.apply (joint (uniformize (aliceView ρ)))) ε at hp
  rw [← relabel_physical (aliceView ρ) copyLabel,
    ← relabel_physical (uniformize (aliceView ρ)) copyLabel, repaired_factor] at hp
  exact ((repair_close ρ).trans hp).weaken (by linarith)

theorem mass_ideal (ρ : State ((K × K) × T) e) : mass (ideal ρ) = mass ρ := by
  rw [ideal, mass_relabel, mass_uniformize, aliceView, mass_relabel]

end
end Foundation.Quantum.QKD.CommonKey
