import Foundation.Quantum.QKD.HashCollision
import Foundation.Quantum.QKD.CommonKeyComposition
import Foundation.Quantum.QKD.SeededSubnormalized

/-! Fresh public hashing verifies an arbitrary pair of classical keys. The
same quantum blocks and their original weights are retained on both branches.
The verification seed must be sampled independently after the input state;
this is not authentication of the public communication. -/
namespace Foundation.Quantum.QKD.KeyVerification
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {K T S V : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype V]
    [DecidableEq K] [DecidableEq T] [DecidableEq S] [DecidableEq V] {e : Space}

abbrev Input (K T : Type) := (K × K) × T
abbrev Public (T S V : Type) := (T × S) × V

def passes (hash : S → K → V) (x : S × Input K T) : Prop :=
  hash x.1 x.2.1.1 = hash x.1 x.2.1.2

instance passesDecidable (hash : S → K → V) : DecidablePred (passes (T := T) hash) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

def transcript (hash : S → K → V) (x : S × Input K T) : Public T S V :=
  ((x.2.2,x.1), hash x.1 x.2.1.1)

def acceptLabel (hash : S → K → V) (x : S × Input K T) : Input K (Public T S V) :=
  (x.2.1,transcript hash x)

/-- The receiver accepts precisely when its local tag matches the public tag. -/
def accepted (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V) :=
  relabel (restrict (seed p ρ) (passes hash)) (acceptLabel hash)

/-- A failed check still publishes the same seed and Alice's tag. -/
def aborted (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V) :=
  relabel (restrict (seed p ρ) (fun x => ¬ passes hash x)) (transcript hash)

theorem branch_mass (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V) :
    mass (accepted ρ p hash) + mass (aborted ρ p hash) = mass ρ := by
  rw [accepted, aborted, mass_relabel, mass_relabel, mass_partition, mass_seed]

/-- No normalization by the passing probability occurs. -/
theorem correctness_expansion (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V) :
    CommonKey.correctnessError (accepted ρ p hash) =
      ∑ x, if x.1.1 = x.1.2 then 0 else
        Collision.collision p hash x.1.1 x.1.2 * (ρ.block x).trace.re := by
  have he : CommonKey.correctnessError (accepted ρ p hash) =
      mass (restrict (accepted ρ p hash) (fun x => x.1.1 ≠ x.1.2)) := by
    rw [mass_restrict]
    unfold CommonKey.correctnessError
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x.1.1 = x.1.2 <;> simp [hx]
  rw [he, accepted, restrict_relabel, mass_relabel]
  simp only [mass, restrict, seed, acceptLabel, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    apply_ite, Matrix.trace_zero, Complex.zero_re, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hx : x = y
  · simp [hx]
  · simp only [hx, ne_eq, not_false_eq_true, ite_true, ite_false, passes,
      Collision.collision, eventProb_toReal, Finset.sum_mul, ite_mul, zero_mul]

theorem correctness_le (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V)
    (κ : ℝ) (hc : ∀ a b, a ≠ b → Collision.collision p hash a b ≤ κ) :
    CommonKey.correctnessError (accepted ρ p hash) ≤ κ * CommonKey.correctnessError ρ := by
  rw [correctness_expansion, CommonKey.correctnessError, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x.1.1 = x.1.2
  · simp [hx]
  · simp only [hx, ite_false]
    exact mul_le_mul_of_nonneg_right (hc _ _ hx)
      (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1

omit [DecidableEq T] in
/-- The mismatch is an event in a state of mass at most one. -/
theorem input_correctness_le_mass (ρ : State (Input K T) e) :
    CommonKey.correctnessError ρ ≤ mass ρ := by
  unfold CommonKey.correctnessError mass
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x.1.1 = x.1.2
  · simp only [hx, ite_true]
    exact (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1
  · simp only [hx, ite_false]
    rfl

theorem correctness_budget (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V)
    (κ : ℝ) (hκ : 0 ≤ κ) (hc : ∀ a b, a ≠ b → Collision.collision p hash a b ≤ κ) :
    CommonKey.correctnessError (accepted ρ p hash) ≤ κ := by
  calc
    _ ≤ κ * CommonKey.correctnessError ρ := correctness_le ρ p hash κ hc
    _ ≤ κ * mass ρ := mul_le_mul_of_nonneg_left (input_correctness_le_mass ρ) hκ
    _ ≤ κ * 1 := mul_le_mul_of_nonneg_left ρ.bounded hκ
    _ = κ := mul_one κ

end
end Foundation.Quantum.QKD.KeyVerification
