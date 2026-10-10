import Foundation.Quantum.QKD.QuantumErrorTest
import Foundation.Quantum.RecordObservation

/-! Measuring a finite function of basis labels preserves every coherence
inside one fiber. In particular a sample measurement need not measure the
untested registers or an adversary's quantum system. -/
namespace Foundation.Quantum.PartitionMeasurement
noncomputable section
set_option backward.isDefEq.respectTransparency false
open QKD.QuantumErrorTest
variable {a : Space} {m : Nat}

def instrument (f : a.Basis → Fin m) : Instrument a a m where
  branch r := Kraus.single (mask (fun i => f i = r))
  complete := by
    simp only [Kraus.single_effect, mask_adjoint]
    ext i j
    simp [mask, Matrix.sum_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
      Matrix.one_apply, -Finset.sum_boole]

theorem branch_entry (f : a.Basis → Fin m) (ρ : Operator a) (r : Fin m) (i j : a.Basis) :
    ((instrument f).branch r).apply ρ i j =
      if f i = r ∧ f j = r then ρ i j else 0 := by
  simp only [instrument, Kraus.single_apply, mask_adjoint]
  by_cases hi : f i = r <;> by_cases hj : f j = r <;>
    simp [mask, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]

theorem probability (f : a.Basis → Fin m) (ρ : Density a) (r : Fin m) :
    (instrument f).probability ρ r =
      (∑ i, if f i = r then ρ.matrix i i else 0).re := by
  unfold Instrument.probability Matrix.trace Matrix.diag
  simp_rw [branch_entry]
  simp only [and_self]

theorem event_probability (f : a.Basis → Fin m) (P : Fin m → Prop) [DecidablePred P]
    (ρ : Density a) :
    (recordEvent a P).probability ((instrument f).record.run ρ) =
      (∑ i, if P (f i) then ρ.matrix i i else 0).re := by
  rw [recordEvent_probability]
  simp_rw [Instrument.record_label_weight, probability]
  have real_ite (r : Fin m) :
      (if P r then (∑ i, if f i = r then ρ.matrix i i else 0).re else 0) =
      (if P r then ∑ i, if f i = r then ρ.matrix i i else 0 else 0).re := by
    split_ifs <;> simp
  simp_rw [real_ite]
  rw [← Complex.re_sum]
  congr 1
  have dist (r : Fin m) :
      (if P r then ∑ i, if f i = r then ρ.matrix i i else 0 else 0) =
      ∑ i, if f i = r then (if P r then ρ.matrix i i else 0) else 0 := by
    by_cases h : P r <;> simp [h]
  simp_rw [dist]
  rw [Finset.sum_comm]
  simp

/-- Coarse acceptance has the same weight as reading the complete sample
record. Their postmeasurement states are deliberately not identified. -/
theorem acceptance (f : a.Basis → Fin m) (P : Fin m → Prop) [DecidablePred P]
    (ρ : Density a) :
    (test (fun i => P (f i))).probability ρ 0 =
      (recordEvent a P).probability ((instrument f).record.run ρ) := by
  rw [event_probability]
  unfold Instrument.probability
  change ((Kraus.single (mask (fun i => if (0:Fin 2) = 0 then P (f i) else ¬ P (f i)))).apply
    ρ.matrix).trace.re = _
  simp only [Kraus.single_apply, mask_adjoint]
  simp only [mask, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.trace, Matrix.diag,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P (f i) <;> simp [h]

end
end Foundation.Quantum.PartitionMeasurement
