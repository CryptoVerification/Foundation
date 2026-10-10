import Foundation.Quantum.QKD.RepetitionReconciliation
import Foundation.Quantum.QKD.CommonKeyComposition
import Foundation.Quantum.QKD.SeededSubnormalized

/-! The concrete decoder on any classical-quantum input, retaining Eve's
conditional quantum states and the public syndrome. No independence of
blocks, or of Eve, is assumed. -/
namespace Foundation.Quantum.QKD.RepetitionReconciliation
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

/-- The same public map acting on all conditional quantum components. -/
def process {b : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) := relabel ρ reconcile

/-- Bob's actual decoding changes neither Alice's word nor the message in
her public-key marginal. This is an equality of conditional quantum states. -/
theorem process_alice_view {b : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    CommonKey.aliceView (process ρ) =
      relabel ρ (fun x => (x.1, blockMessage x.1)) := by
  unfold CommonKey.aliceView process
  rw [relabel_comp]
  rfl

theorem process_mass {b : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    mass (process ρ) = mass ρ := mass_relabel ρ reconcile

/-- Failure is charged only to inputs with two or more errors in some triple.
This is a bound by the actual bad-event weight, not yet a sampling estimate. -/
theorem process_correctness {b : Nat} {e : Space}
    (ρ : State ((Fin b → Triple) × (Fin b → Triple)) e) :
    CommonKey.correctnessError (process ρ) ≤
      mass (restrict ρ (fun x => ∃ j, 1 < errors (x.1 j) (x.2 j))) := by
  have he : CommonKey.correctnessError (process ρ) =
      mass (restrict (process ρ) (fun x => x.1.1 ≠ x.1.2)) := by
    rw [mass_restrict]
    unfold CommonKey.correctnessError
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x.1.1 = x.1.2 <;> simp [h]
  rw [he, process, restrict_relabel, mass_relabel, mass_restrict, mass_restrict]
  apply Finset.sum_le_sum
  intro x _
  by_cases hbad : ∃ j, 1 < errors (x.1 j) (x.2 j)
  · simp only [hbad, ite_true]
    split_ifs
    · rfl
    · exact (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1
  · have hc : ∀ j, errors (x.1 j) (x.2 j) ≤ 1 := by
      intro j
      by_contra hj
      exact hbad ⟨j, by omega⟩
    simp only [reconcile_correct x.1 x.2 hc, ne_eq, not_true_eq_false, hbad, ite_false]
    rfl

end
end Foundation.Quantum.QKD.RepetitionReconciliation
