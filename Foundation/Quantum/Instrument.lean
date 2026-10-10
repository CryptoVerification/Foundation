import Foundation.Quantum.Effects

/-! Instruments retain a finite classical outcome and a quantum output.
Branches are subnormalized; conditioning on a zero-probability outcome is not performed. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

structure Instrument (a b : Space) (outcomes : Nat) where
  branch : Fin outcomes → Kraus a b
  complete : ∑ r, (branch r).effect = 1

namespace Instrument
variable {a b : Space} {n : Nat}

def forget (I : Instrument a b n) : Channel a b where
  index := (r : Fin n) × (I.branch r).index
  finite := inferInstance
  operator p := (I.branch p.1).operator p.2
  complete := by simpa [Kraus.effect, Fintype.sum_sigma] using I.complete

theorem forget_apply (I : Instrument a b n) (ρ : Operator a) :
    I.forget.toKraus.apply ρ = ∑ r, (I.branch r).apply ρ := by
  simp [forget, Kraus.apply, Fintype.sum_sigma]

def probability (I : Instrument a b n) (ρ : Density a) (r : Fin n) : ℝ :=
  ((I.branch r).apply ρ.matrix).trace.re

theorem probability_nonneg (I : Instrument a b n) (ρ : Density a) (r : Fin n) :
    0 ≤ I.probability ρ r :=
  (Complex.nonneg_iff.mp ((I.branch r).positive ρ.positive).trace_nonneg).1

theorem probability_sum (I : Instrument a b n) (ρ : Density a) :
    ∑ r, I.probability ρ r = 1 := by
  have h := (I.forget.run ρ).normalized
  change (I.forget.toKraus.apply ρ.matrix).trace = 1 at h
  rw [I.forget_apply, Matrix.trace_sum] at h
  simpa [probability, Complex.re_sum] using congrArg Complex.re h

theorem probability_le_one (I : Instrument a b n) (ρ : Density a) (r : Fin n) :
    I.probability ρ r ≤ 1 := by
  rw [← I.probability_sum ρ]
  exact Finset.single_le_sum (fun s _ => I.probability_nonneg ρ s) (Finset.mem_univ r)

/-- Embedding a branch output with its classical label. -/
def recordOperator (r : Fin n) (M : Op a b) : Op a (.tensor (.register n) b) :=
  fun i j => if i.1 = r then M i.2 j else 0

theorem recordOperator_gram (r : Fin n) (M : Op a b) :
    (recordOperator r M).conjTranspose * recordOperator r M = M.conjTranspose * M := by
  ext i j
  change (∑ p : Fin n × b.Basis, star (if p.1 = r then M p.2 i else 0) *
    (if p.1 = r then M p.2 j else 0)) = ∑ p : b.Basis, star (M p i) * M p j
  simp [Fintype.sum_prod_type, apply_ite, ite_mul]

/-- A physical channel outputs the classical register together with the quantum system. -/
def record (I : Instrument a b n) : Channel a (.tensor (.register n) b) where
  index := (r : Fin n) × (I.branch r).index
  finite := inferInstance
  operator p := recordOperator p.1 ((I.branch p.1).operator p.2)
  complete := by
    change (∑ p : (r : Fin n) × (I.branch r).index,
      (recordOperator p.1 ((I.branch p.1).operator p.2)).conjTranspose *
        recordOperator p.1 ((I.branch p.1).operator p.2)) = 1
    simp only [recordOperator_gram (a := a) (b := b)]
    simpa [Kraus.effect, Fintype.sum_sigma] using I.complete

end Instrument
end
end Foundation.Quantum
