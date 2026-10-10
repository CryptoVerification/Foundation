import Foundation.Quantum.InstrumentMarginal
import Foundation.Quantum.ClassicalMap
import Foundation.Quantum.ProbabilityBridge

/-! Observations of a recorded classical output agree with the corresponding
PMF events, while the quantum output is retained. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder

/-- The physical binary test of an arbitrary predicate on a recorded classical label. -/
def recordEvent {n : Nat} (b : Space) (P : Fin n → Prop) [DecidablePred P] :
    Effect (.tensor (.register n) b) where
  matrix := Matrix.diagonal (fun i => if P i.1 then 1 else 0)
  positive := Matrix.posSemidef_diagonal_iff.mpr (by intro i; split_ifs <;> simp)
  complement_positive := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> simp

theorem recordEvent_probability {n : Nat} (b : Space) (P : Fin n → Prop) [DecidablePred P]
    (ρ : Density (.tensor (.register n) b)) :
    (recordEvent b P).probability ρ =
      ∑ r : Fin n, if P r then (∑ i : b.Basis, ρ.matrix (r,i) (r,i)).re else 0 := by
  simp [Effect.probability, recordEvent, Matrix.trace, Matrix.diagonal_mul,
    Fintype.sum_prod_type, ite_mul]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : P r <;> simp [h]

/-- Finite PMF events can be read as the real sum of their point masses. -/
theorem eventProb_toReal {ι : Type*} [Fintype ι] (p : PMF ι) (P : ι → Prop) [DecidablePred P] :
    (Foundation.Probability.eventProb p P).toReal = ∑ i, if P i then (p i).toReal else 0 := by
  unfold Foundation.Probability.eventProb
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : P i <;> simp [h]
  · intro i _
    by_cases h : P i <;> simp [h, p.apply_ne_top]


/-- PMF event probabilities are finite even when the sample type is infinite. -/
theorem eventProb_ne_top {ι : Type*} (p : PMF ι) (P : ι → Prop) :
    Foundation.Probability.eventProb p P ≠ ⊤ := by
  have hu : p.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa only [Set.indicator_univ] using p.tsum_coe
  have h := p.toOuterMeasure.mono (Set.subset_univ {i | P i})
  change p.toOuterMeasure {i | P i} ≤ p.toOuterMeasure Set.univ at h
  rw [hu] at h
  exact ne_top_of_le_ne_top ENNReal.one_ne_top h

theorem eventProb_bind_toReal {ι κ : Type*} [Fintype ι] (p : PMF ι) (f : ι → PMF κ)
    (P : κ → Prop) :
    (Foundation.Probability.eventProb (p.bind f) P).toReal =
      ∑ i, (p i).toReal * (Foundation.Probability.eventProb (f i) P).toReal := by
  unfold Foundation.Probability.eventProb
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro i _
    exact ENNReal.mul_ne_top (p.apply_ne_top i) (eventProb_ne_top (f i) P)


/-- Relabelling a classical record pulls a predicate back along the actual relabelling function. -/
theorem classicalMap_recordEvent {n m : Nat} (a : Space) (f : Fin n → Fin m)
    (P : Fin m → Prop) [DecidablePred P] :
    ((classicalMap a f).pullEffect (recordEvent a P)).matrix =
      (recordEvent a (fun r => P (f r))).matrix := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp [Channel.pullEffect, Kraus.dual, classicalMap, classicalMapOperator, recordEvent,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    Fintype.sum_prod_type, ite_and, apply_ite, eq_comm,
    -Finset.sum_boole]
  split_ifs <;> simp_all

namespace Instrument
variable {a b : Space} {n : Nat}

theorem record_diagonal (I : Instrument a b n) (ρ : Operator a)
    (r : Fin n) (i j : b.Basis) :
    I.record.toKraus.apply ρ (r,i) (r,j) = (I.branch r).apply ρ i j := by
  simp [record, Kraus.apply, recordOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_sigma, ite_mul]

theorem record_label_weight (I : Instrument a b n) (ρ : Density a) (r : Fin n) :
    (∑ i : b.Basis, (I.record.run ρ).matrix (r,i) (r,i)).re = I.probability ρ r := by
  change (∑ i : b.Basis, I.record.toKraus.apply ρ.matrix (r,i) (r,i)).re = _
  exact congrArg Complex.re (Finset.sum_congr rfl (fun i _ => record_diagonal I ρ.matrix r i i))


/-- Every classical predicate has the same probability in the quantum record and its PMF interface. -/
theorem record_event (I : Instrument a b n) (ρ : Density a) (P : Fin n → Prop) [DecidablePred P] :
    (recordEvent b P).probability (I.record.run ρ) =
      (Foundation.Probability.eventProb (I.classicalOutcome ρ) P).toReal := by
  rw [recordEvent_probability, eventProb_toReal]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · rw [record_label_weight]
    exact (ENNReal.toReal_ofReal (I.probability_nonneg ρ r)).symm
  · rfl


/-- Physical deterministic processing of a record preserves the PMF event interpretation. -/
theorem encoded_record_event {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Instrument a b n) (ρ : Density a) (f : Fin n → κ) (P : κ → Prop) [DecidablePred P] :
    (recordEvent b (fun r => P ((Fintype.equivFin κ).symm r))).probability
      ((classicalMap b (fun r => Fintype.equivFin κ (f r))).run (I.record.run ρ)) =
      (Foundation.Probability.eventProb ((I.classicalOutcome ρ).map f) P).toReal := by
  rw [Effect.probability_run]
  have he := classicalMap_recordEvent b (fun r => Fintype.equivFin κ (f r))
    (fun r => P ((Fintype.equivFin κ).symm r))
  simp only [Equiv.symm_apply_apply] at he
  change (_ * (I.record.run ρ).matrix).trace.re = _
  rw [he]
  change (recordEvent b (fun r => P (f r))).probability (I.record.run ρ) = _
  rw [record_event]
  unfold Foundation.Probability.eventProb
  rw [PMF.toOuterMeasure_map_apply]
  rfl

end Instrument
end
end Foundation.Quantum
