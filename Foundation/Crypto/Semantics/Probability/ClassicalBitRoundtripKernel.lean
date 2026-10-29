import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitKeyTest
import Foundation.Crypto.Semantics.Probability.FiniteMaximalKernel

/-! A concrete round trip of the selected maximal kernels on the sharp table
edge. Its endpoint law is preserved, but its conditional kernel mixes two
reachable keys. This audits composition; no novelty assertion is made. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip
open Foundation.Probability FiniteMaximalCoupling
open scoped BigOperators ENNReal
noncomputable section

abbrev Result := Fin 5 × Bool

def p (message : Bool) := tableEightBitLaw (sharpTableChain 0) message
def q (message : Bool) := tableEightBitLaw (sharpTableChain 2) message

def sourceCount (message : Bool) (r : Result) : ℕ :=
  if r = (0,message) then 128 else if r = (2,!message) then 128 else 0

def targetCount (message : Bool) (r : Result) : ℕ :=
  if r = (0,message) then 88 else if r = (1,message) then 20 else
  if r = (2,!message) then 94 else if r = (3,message) then 20 else
  if r = (4,!message) then 34 else 0

theorem source_count (message : Bool) (r : Result) :
    tableAtomCount (sharpTableChain 0) message r = sourceCount message r := by
  rcases r with ⟨key, ciphertext⟩
  fin_cases key <;> cases message <;> cases ciphertext <;> decide +kernel

theorem target_count (message : Bool) (r : Result) :
    tableAtomCount (sharpTableChain 2) message r = targetCount message r := by
  rcases r with ⟨key, ciphertext⟩
  fin_cases key <;> cases message <;> cases ciphertext <;> decide +kernel

theorem p_real (message : Bool) (r : Result) : (p message r).toReal = (sourceCount message r : ℝ) / 256 := by
  rw [p, table_atom_real_count, source_count]

theorem q_real (message : Bool) (r : Result) : (q message r).toReal = (targetCount message r : ℝ) / 256 := by
  rw [q, table_atom_real_count, target_count]

theorem source_supported (message : Bool) : (0,message) ∈ (p message).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  have hr := p_real message (0,message)
  rw [h] at hr
  norm_num [sourceCount] at hr

theorem forward_residual (message : Bool) : FiniteMaximalCoupling.residual (p message) (q message) = 37 / 128 := by
  unfold FiniteMaximalCoupling.residual FiniteMaximalCoupling.common
  simp only [p_real, q_real, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  cases message <;> norm_num [sourceCount, targetCount, Fin.ext_iff]

theorem reverse_residual (message : Bool) : FiniteMaximalCoupling.residual (q message) (p message) = 37 / 128 := by
  unfold FiniteMaximalCoupling.residual FiniteMaximalCoupling.common
  simp only [p_real, q_real, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  cases message <;> norm_num [sourceCount, targetCount, Fin.ext_iff]

theorem kernel_real {α : Type} [Fintype α] (a b : PMF α) (x y : α) :
    (kernel a b x y).toReal = if (a x).toReal = 0 then (b y).toReal else FiniteMaximalCoupling.mass a b x y / (a x).toReal := by
  by_cases h : (a x).toReal = 0
  · simp only [kernel, dif_pos h, if_pos h]
  · simp only [kernel, dif_neg h, if_neg h, PMF.ofFintype_apply,
      ENNReal.toReal_ofReal (div_nonneg (FiniteMaximalCoupling.mass_nonneg a b x y) ENNReal.toReal_nonneg)]

def roundtrip (message : Bool) (x : Result) : PMF Result :=
  (kernel (p message) (q message) x).bind (kernel (q message) (p message))

theorem preserves (message : Bool) : (p message).bind (roundtrip message) = p message := by
  unfold roundtrip
  rw [← PMF.bind_bind, kernel_preserve, kernel_preserve]

theorem changes_key (message : Bool) :
    (roundtrip message (0,message) (2,!message)).toReal = 85 / 592 := by
  unfold roundtrip
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun r _ =>
    ENNReal.mul_ne_top ((kernel (p message) (q message) (0,message)).apply_ne_top r)
      ((kernel (q message) (p message) r).apply_ne_top (2,!message)))]
  simp only [ENNReal.toReal_mul, kernel_real, FiniteMaximalCoupling.mass, FiniteMaximalCoupling.common, FiniteMaximalCoupling.left, FiniteMaximalCoupling.right,
    forward_residual, reverse_residual, p_real, q_real,
    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  cases message <;> norm_num [sourceCount, targetCount, Fin.ext_iff]

theorem not_identity (message : Bool) : roundtrip message (0,message) ≠ PMF.pure (0,message) := by
  intro h
  have hc := changes_key message
  rw [h] at hc
  norm_num [PMF.pure_apply] at hc

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip
