import Foundation.Quantum.Instrument
import Foundation.Quantum.OneTimePad
import Foundation.Crypto.Semantics.Probability.Comp

/-! Measurement records and single-use quantum distinguishers expose classical
outputs through the project's existing PMF-based ProbComp interface. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Instrument

def classicalOutcome {a b n} (I : Instrument a b n) (ρ : Density a) :
    Foundation.Probability.ProbComp (Fin n) :=
  PMF.ofFintype (fun r => ENNReal.ofReal (I.probability ρ r)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => I.probability_nonneg ρ r),
      I.probability_sum]
    simp)

theorem classicalOutcome_event {a b n} (I : Instrument a b n) (ρ : Density a) (r : Fin n) :
    Foundation.Probability.eventProb (I.classicalOutcome ρ) (fun s => s = r) =
      ENNReal.ofReal (I.probability ρ r) := by
  change (I.classicalOutcome ρ).toOuterMeasure {r} = _
  rw [PMF.toOuterMeasure_apply_singleton]
  rfl
end Instrument

namespace Adversary
variable {a b : Space}

/-- A classical challenge result sampled with the actual quantum acceptance probability. -/
def experiment (A : Adversary a b) (C : Channel a b) : Foundation.Probability.ProbComp Bool :=
  PMF.ofFintype (fun result => ENNReal.ofReal
    (if result then A.acceptance C else 1 - A.acceptance C)) (by
    have h0 : 0 ≤ A.acceptance C := A.test.probability_nonneg _
    have h1 : A.acceptance C ≤ 1 := A.test.probability_le_one _
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro r _; cases r <;> simp_all)]
    simp)

theorem experiment_acceptance (A : Adversary a b) (C : Channel a b) :
    Foundation.Probability.eventProb (A.experiment C) (fun result => result = true) =
      ENNReal.ofReal (A.acceptance C) := by
  change (A.experiment C).toOuterMeasure {true} = _
  rw [PMF.toOuterMeasure_apply_singleton]
  rfl
end Adversary

/-- Perfect privacy is a zero gap in the existing classical observation semantics. -/
theorem oneTimePad_existing_probability (A : Adversary .bit .bit) :
    Foundation.Probability.probabilityGap
      (Foundation.Probability.eventProb (A.experiment OneTimePad.average) (fun b => b = true))
      (Foundation.Probability.eventProb (A.experiment OneTimePad.ideal) (fun b => b = true)) = 0 := by
  have h := (approx_iff_adversaries _ _ _).mp OneTimePad.perfect_privacy A
  have he : A.acceptance OneTimePad.average = A.acceptance OneTimePad.ideal :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  rw [Adversary.experiment_acceptance, Adversary.experiment_acceptance, he]
  simp [Foundation.Probability.probabilityGap]

end
end Foundation.Quantum
